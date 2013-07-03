{-# LANGUAGE TupleSections #-}

module GHC.NT.Plugin where

import GhcPlugins
import MkId
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
    coAxiomU <- getUniqueM
    coAxiomNameU <- getUniqueM
    let cot = mkCoercionType (mkTyVarTy a) (mkTyVarTy b)
        rett = mkTyConApp t' arg_tys
        dct = mkForAllTys [a,b] $ mkFunTy cot rett
        -- Have to use the original name, otherwise we get a 
        -- urk! lookup local fingerprint
        --tcn = mkExternalName tyConU mod (mkTcOcc "NT") noSrcSpan
        tcn = tyConName oldTyCon
        n = mkExternalName dataConU mod (mkDataOcc "NT") noSrcSpan
        coAxiomN = mkExternalName coAxiomNameU mod (mkNewTyCoOcc (occName (tcn))) noSrcSpan
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
        coa = CoAxiom
                coAxiomU
                coAxiomN
                [a,b]
                rett
                cot
                True
        t' = mkAlgTyCon
               tcn 
               (mkArrowKinds [liftedTypeKind, liftedTypeKind] liftedTypeKind)
               [a,b]
               Nothing
               []
               (NewTyCon dc' cot ([a,b], cot) coa)
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
    au <- getUniqueM
    bu <- getUniqueM
    ntu <- getUniqueM
    nttu <- getUniqueM
    xu <- getUniqueM
    cou <- getUniqueM
    let a   = mkTyVar (mkSystemName au (mkTyVarOcc "a")) liftedTypeKind
        b   = mkTyVar (mkSystemName bu (mkTyVarOcc "b")) liftedTypeKind
        ntt = mkTyConApp nttc [mkTyVarTy a, mkTyVarTy b]
        nt  = mkLocalVar VanillaId (mkSystemName ntu (mkVarOcc "nt")) ntt vanillaIdInfo
        x   = mkLocalVar VanillaId (mkSystemName xu (mkVarOcc "b")) (mkTyVarTy a) vanillaIdInfo
        co = mkCoVar (mkSystemName cou (mkTyVarOcc "co")) (mkCoercionType (mkTyVarTy a) (mkTyVarTy b))
        coAxiom = newTyConCo nttc
    let e' = Lam a $ Lam b $ Lam nt $ Lam x $
                App (Lam co (Cast (Var x) (CoVarCo co))) $ 
                Cast (Var nt) (AxiomInstCo coAxiom [Refl (mkTyVarTy a), Refl (mkTyVarTy b)])
    return (NonRec v e')

bind nttc b@(NonRec v e) | getOccString v == "refl" = do
    a <- createTyVar "a"
    let [dc] = tyConDataCons nttc
    let e' = Lam a $ mkConApp dc
                    [ Type (mkTyVarTy a)
                    , Type (mkTyVarTy a)
                    , Coercion (Refl (mkTyVarTy a))
                    ]
    return (NonRec v e')

bind nttc b@(NonRec v e) | getOccString v == "sym" = do
    a <- createTyVar "a"
    b <- createTyVar "b"
    ntu <- getUniqueM
    nttu <- getUniqueM
    cou <- getUniqueM
    let ntt = mkTyConApp nttc [mkTyVarTy a, mkTyVarTy b]
        ntt' = mkTyConApp nttc [mkTyVarTy b, mkTyVarTy a]
        nt  = mkLocalVar VanillaId (mkSystemName ntu (mkVarOcc "nt")) ntt vanillaIdInfo
        co = mkCoVar (mkSystemName cou (mkTyVarOcc "co")) (mkCoercionType (mkTyVarTy a) (mkTyVarTy b))
        [dc] = tyConDataCons nttc
        coAxiom = newTyConCo nttc
    let e' = Lam a $ Lam b $ Lam nt $
                App (Lam co $ mkConApp dc
                    [ Type (mkTyVarTy b)
                    , Type (mkTyVarTy a)
                    , Coercion (SymCo (CoVarCo co))
                    ]
                ) $
                Cast (Var nt) (AxiomInstCo coAxiom [Refl (mkTyVarTy a), Refl (mkTyVarTy b)])
    return (NonRec v e')

bind nttc b@(NonRec v e) | getOccString v == "trans" = do
    a <- createTyVar "a"
    b <- createTyVar "b"
    c <- createTyVar "c"
    ntu <- getUniqueM
    nt2u <- getUniqueM
    nttu <- getUniqueM
    ntt'u <- getUniqueM
    cou <- getUniqueM
    co2u <- getUniqueM
    let ntt = mkTyConApp nttc [mkTyVarTy a, mkTyVarTy b]
        nt2t = mkTyConApp nttc [mkTyVarTy b, mkTyVarTy c]
        ntt' = mkTyConApp nttc [mkTyVarTy a, mkTyVarTy c]
        nt  = mkLocalVar VanillaId (mkSystemName ntu (mkVarOcc "nt")) ntt vanillaIdInfo
        nt2  = mkLocalVar VanillaId (mkSystemName nt2u (mkVarOcc "nt2")) nt2t vanillaIdInfo
        co = mkCoVar (mkSystemName cou (mkTyVarOcc "co")) (mkCoercionType (mkTyVarTy a) (mkTyVarTy b))
        co2 = mkCoVar (mkSystemName co2u (mkTyVarOcc "co2")) (mkCoercionType (mkTyVarTy b) (mkTyVarTy c))
        [dc] = tyConDataCons nttc
        coAxiom = newTyConCo nttc
    let e' = Lam a $ Lam b $ Lam c $ Lam nt $ Lam nt2 $
                App (Lam co $ 
                    App (Lam co2 $ mkConApp dc
                        [ Type (mkTyVarTy a)
                        , Type (mkTyVarTy c)
                        , Coercion (TransCo (CoVarCo co) (CoVarCo co2))
                        ]
                    ) $
                    Cast (Var nt2) (AxiomInstCo coAxiom [Refl (mkTyVarTy b), Refl (mkTyVarTy c)])

                ) $
                Cast (Var nt) (AxiomInstCo coAxiom [Refl (mkTyVarTy a), Refl (mkTyVarTy b)])
    return (NonRec v e')

bind nttc b@(NonRec v e) | getOccString v == "listNT" = do
    a <- createTyVar "a"
    b <- createTyVar "b"
    ntu <- getUniqueM
    nttu <- getUniqueM
    ntt'u <- getUniqueM
    cou <- getUniqueM
    let ntt = mkTyConApp nttc [mkTyVarTy a, mkTyVarTy b]
        ntt' = mkTyConApp nttc [mkTyConApp listTyCon [mkTyVarTy a], mkTyConApp listTyCon [mkTyVarTy b]]
        nt  = mkLocalVar VanillaId (mkSystemName ntu (mkVarOcc "nt")) ntt vanillaIdInfo
        co = mkCoVar (mkSystemName cou (mkTyVarOcc "co")) (mkCoercionType (mkTyVarTy a) (mkTyVarTy b))
        [dc] = tyConDataCons nttc
        coAxiom = newTyConCo nttc
    let e' = Lam a $ Lam b $ Lam nt $
            App (Lam co $ mkConApp dc
                    [ Type (mkTyConApp listTyCon [mkTyVarTy a])
                    , Type (mkTyConApp listTyCon [mkTyVarTy b])
                    ,  Coercion (TyConAppCo listTyCon [CoVarCo co])
                    ]
            ) $
            Cast (Var nt) (AxiomInstCo coAxiom [Refl (mkTyVarTy a), Refl (mkTyVarTy b)])
    return (NonRec v e')

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

        --putMsg (ppr e)
        -- Extract the typcon from f's type
        let nttc = tyConAppTyCon (exprType e)
        let [dc] = tyConDataCons nttc
        let e' = mkConApp dc [ Type ta, Type tb, Coercion (mkAxInstCo coa tyArgs)] :: CoreExpr
        --putMsg (ppr nttc)
        --putMsg (ppr (tyConDataCons nttc))
        --putMsg (ppr e')
        return (Just e')
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
