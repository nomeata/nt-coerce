import Test.Framework.TestManager
import Test.Framework.BlackBoxTest

main = do
    bbts <- blackBoxTests "tests" "/bin/bash" ".run" defaultBBTArgs
    htfMain (makeTestSuite "Tests" bbts)
