{-# LANGUAGE TupleSections #-}

module GHC.NT.Plugin where

import GhcPlugins
import MkId
import Pair
import Kind

import Control.Monad
import Control.Applicative
import Data.Functor
import Data.Maybe

plugin :: Plugin
plugin = defaultPlugin {
    installCoreToDos = install
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ xs = do
    reinitializeGlobals
    return $ CoreDoPasses [nt,nt2] : xs
  where nt = CoreDoPluginPass "GHC.NT implementation" ntPass
        nt2 = CoreDoPluginPass "GHC.NT.createNT implementation" nt2Pass

ntPass :: ModGuts -> CoreM ModGuts
ntPass g | moduleNameString (moduleName (mg_module g)) == "GHC.NT.Type" = do
    let [oldTc] = mg_tcs g
    nttc <- createNTTyCon (mg_module g) oldTc
    tcs' <- mapM (replaceTyCon nttc) (mg_tcs g)

    return $ g { mg_tcs = tcs' }
ntPass g | moduleNameString (moduleName (mg_module g)) == "GHC.NT" = do
    nttc <- lookupNTTyCon (mg_rdr_env g) (mg_module g)
    binds' <- mapM (bind nttc) (mg_binds g)

    return $ g { mg_binds = binds' }
ntPass g = return g

nt2Pass :: ModGuts -> CoreM ModGuts
nt2Pass = bindsOnlyPass $ mapM (traverseBind replaceCreateNT)

createNTTyCon :: Module -> TyCon -> CoreM TyCon
createNTTyCon mod oldTyCon = do
    a <- createTyVar "a"
    b <- createTyVar "b"
    let arg_tys = map mkTyVarTy [a,b]
    let tyConU = tyConUnique oldTyCon
    dataConU <- getUniqueM
    dataConWorkerU <- getUniqueM
    dataConWrapperU <- getUniqueM
    let cot = mkCoercionType (mkTyVarTy a) (mkTyVarTy b)
        rett = mkTyConApp t' arg_tys
        dct = mkForAllTys [a,b] $ mkFunTy cot rett
        -- Have to use the original name, otherwise we get a 
        -- urk! lookup local fingerprint
        --tcn = mkExternalName tyConU mod (mkTcOcc "NT") noSrcSpan
        tcn = tyConName oldTyCon
        n = mkExternalName dataConU mod (mkDataOcc "NT") noSrcSpan
        dataConWorkerN = mkSystemName dataConWorkerU (mkDataOcc "NT_work")
        dataConWrapperN = mkSystemName dataConWrapperU (mkDataOcc "NT_wrap")
        workId = mkGlobalId (DataConWrapId dc') dataConWorkerN dct vanillaIdInfo
        dataConIds = mkDataConIds dataConWorkerN dataConWrapperN dc'
        dc' = mkDataCon
                n
                False
                [ HsNoBang ]
                []
                [a,b]
                []
                []
                []
                [ cot ]
                rett
                t'
                []
                dataConIds -- (DCIds Nothing workId)
        t' = mkAlgTyCon
               tcn 
               (mkArrowKinds [liftedTypeKind, liftedTypeKind] liftedTypeKind)
               [a,b]
               Nothing
               []
               (DataTyCon [dc'] False)
               NoParentTyCon
               NonRecursive
               False
    return t'

replaceTyCon :: TyCon -> TyCon -> CoreM TyCon
replaceTyCon nttc t 
    | occNameString (nameOccName (tyConName t)) == "NT" = return nttc
    | otherwise = return t

lookupNTTyCon :: GlobalRdrEnv -> Module -> CoreM TyCon
lookupNTTyCon env mod = do
    let packageId = modulePackageId mod -- HACK!
    let ntTypeModule = mkModule packageId (mkModuleName "GHC.NT.Type")
    let rdrName = mkRdrQual (mkModuleName "GHC.NT.Type") (mkTcOcc "NT")

    let e' = head (head (occEnvElts env)) -- HACK
    
    {-
    putMsg (ppr e')
    putMsg (ppr rdrName)
    putMsg (ppr (lookupGRE_RdrName rdrName env))
    putMsg (ppr (lookupGRE_RdrName (nameRdrName (gre_name e')) env))
    
    let [e] = lookupGRE_RdrName rdrName env
    -}

    let n = gre_name e'
    lookupTyCon n


bind :: TyCon -> CoreBind -> CoreM CoreBind
bind nttc b@(NonRec v e) | getOccString v == "coerce" = do
    NonRec v <$> do
    tyLam "a" $ \a -> do
    tyLam "b" $ \b -> do
    lamNT nttc "co" (mkTyVarTy a) (mkTyVarTy b) $ \co -> do 
    lam "x" (mkTyVarTy a) $ \x -> do
    return $ Cast (Var x) (CoVarCo co)

bind nttc b@(NonRec v e) | getOccString v == "refl" = do
    NonRec v <$> do
    tyLam "a" $ \a ->
        conNT nttc $
            return $ Refl (mkTyVarTy a)

bind nttc b@(NonRec v e) | getOccString v == "sym" = do
    NonRec v <$> do
    tyLam "a" $ \a -> do
    tyLam "b" $ \b -> do
    lamNT nttc "co" (mkTyVarTy a) (mkTyVarTy b) $ \co -> do
    conNT nttc $ do
    return $ SymCo (CoVarCo co)

bind nttc b@(NonRec v e) | getOccString v == "trans" = do
    NonRec v <$> do
    tyLam "a" $ \a -> do
    tyLam "b" $ \b -> do
    tyLam "c" $ \c -> do
    lamNT nttc "co1" (mkTyVarTy a) (mkTyVarTy b) $ \co1 -> do
    lamNT nttc "co2" (mkTyVarTy b) (mkTyVarTy c) $ \co2 -> do
    conNT nttc $ do
    return $ TransCo (CoVarCo co1) (CoVarCo co2)

bind nttc b@(NonRec v e) | getOccString v == "listNT" = do
    NonRec v <$> do
    tyLam "a" $ \a -> do
    tyLam "b" $ \b -> do
    lamNT nttc "co" (mkTyVarTy a) (mkTyVarTy b) $ \co -> do
    conNT nttc $ do
    return $ TyConAppCo listTyCon [CoVarCo co]

bind _ b = do
    --putMsg (ppr b)
    return b

replaceCreateNT :: CoreExpr -> CoreM (Maybe CoreExpr)
replaceCreateNT e@((App (App (Var f) (Type ta)) (Type tb)))
    | getOccString f == "createNT" = do
        -- We exepct ta to be a newtype of tb
        (tc,tyArgs) <- case splitTyConApp_maybe ta of
            Nothing -> error "not a type application"
            Just (tc,tyArgs) -> return (tc,tyArgs)
        (vars,coa) <- case unwrapNewTyCon_maybe tc of
            Nothing -> error "not a newtype"
            Just (vars,_,co) -> return (vars,co)

        -- TODO: Check if all construtors are in scope
        -- TODO: Check that the expanded type of a is actually b

        -- Extract the typcon from f's type
        let nttc = tyConAppTyCon (exprType e)

        Just <$> do
        conNT nttc $ do
        return $ mkAxInstCo coa tyArgs
    | otherwise = do
        --putMsgS $ getOccString f
        return Nothing
replaceCreateNT e = do
    --putMsg (ppr e)
    return Nothing

traverse :: (Functor m, Applicative m, Monad m) => (Expr a -> m (Maybe (Expr a))) -> Expr a -> m (Expr a)
traverse f e
    = f' =<< case e of
        Type t               -> return $ Type t
        Coercion c           -> return $ Coercion c
        Lit lit              -> return $ Lit lit
        Var v                -> return $ Var v
        App fun a            -> App <$> traverse f fun <*> traverse f a
        Tick t e             -> Tick t <$> traverse f e
        Cast e co            -> Cast <$> traverse f e <*> (return co)
        Lam b e              -> Lam b <$> traverse f e
        Let bind e           -> Let <$> traverseBind f bind <*> traverse f e
        Case scrut bndr ty alts -> Case scrut bndr ty <$> mapM (\(a,b,c) -> (a,b,) <$> traverse f c) alts 
    where f' x = do
            r <- f x
            return (fromMaybe x r)

traverseBind :: (Functor m, Applicative m, Monad m) => (Expr a -> m (Maybe (Expr a))) -> Bind a -> m (Bind a)
traverseBind f (NonRec b e) = NonRec b <$> traverse f e
traverseBind f (Rec l) = Rec <$> mapM (\(a,b) -> (a,) <$> traverse f b) l

createTyVar :: String -> CoreM TyVar
createTyVar name = do
    u <- getUniqueM
    return $ mkTyVar (mkSystemName u (mkTyVarOcc name)) liftedTypeKind

tyLam :: String -> (TyVar -> CoreM CoreExpr) -> CoreM CoreExpr
tyLam name body = do 
    v <- createTyVar name
    Lam v <$> body v

lam :: String -> Type -> (Var -> CoreM CoreExpr) -> CoreM CoreExpr
lam name ty body = do 
    u <- getUniqueM
    let v = mkLocalVar VanillaId (mkSystemName u (mkVarOcc name)) ty vanillaIdInfo
    Lam v <$> body v
    
deconNT :: String -> CoreExpr -> (CoVar -> CoreM CoreExpr) -> CoreM CoreExpr
deconNT name nt body = do
    let ntType = exprType nt
    let (nttc, [t1, t2]) = splitTyConApp ntType
    cou <- getUniqueM
    let co = mkCoVar (mkSystemName cou (mkTyVarOcc name)) (mkCoercionType t1 t2)
        [dc] = tyConDataCons nttc
    b <- body co
    return $ mkWildCase nt ntType (exprType b) [(DataAlt dc, [co], b)]

lamNT :: TyCon -> String -> Type -> Type -> (CoVar -> CoreM CoreExpr) -> CoreM CoreExpr
lamNT nttc name t1 t2 body = do
    lam (name ++ "nt") (mkTyConApp nttc [t1, t2]) $ \nt -> do
    deconNT name (Var nt) $ body

conNT :: TyCon -> CoreM Coercion -> CoreM CoreExpr
conNT nttc body = do
    co <- body 
    let Pair t1 t2  = coercionKind co
    return $ mkConApp dc [ Type t1 , Type t2 , Coercion co ]
  where [dc] = tyConDataCons nttc
