{-# LANGUAGE NoImplicitPrelude #-}

-- Use command `stack test --ta '-p "oddEven"'` to test only that file

module Test.Stlc where


import           Prelude hiding (succ,odd,even)
import           SymbolicExecution (topLevel)
import           Printer.Dot
import           Printer.SymTree ()
import           Program.Num
import           Program.Bool (trueo)
import           Syntax
import           System.Directory
import           System.Process   (system)
import           Text.Printf


failure :: G a
failure = (C "Failure1" []) === (C "Failure2" [])

cons x t0 env = C "cons" [x, t0, env]
nil = C "nil" []

evar :: Term a -> Term a
evar x = C "evar" [x]
eabs x b = C "eabs" [x, b]
eapp a b = C "eapp" [a, b]

arrow a b = C "arrow" [a,b]
tvar  n = C "tvar" [n]

disEqPeano :: Def
disEqPeano =
  Def "disEqPeano" ["a", "b"] $
    (call "gto" [a,b,trueo]) ||| (call "lto" [a,b,trueo])
  where
    [a, b] = map V ["a", "b"]

lookupo :: Def
lookupo =
  Def "lookupo" ["env", "x", "ty"] $
    (env === nil &&& failure) |||
    fresh ["tail"] (env === cons x ty tail) |||
    fresh ["b", "t2", "tail"] (env === cons b t2 tail &&& call "disEqPeano" [a,b] &&& call "lookupo" [tail, x, ty])
  where
    [env, a, b, ty, t2, x, x2, tail] = map V ["env", "a", "b", "ty", "t2", "x", "x2", "tail"]



typo =
  Def "typo" ["env", "e", "typ"] $
    fresh ["x"] (e === evar x &&& call "lookupo" [env,x,typ]) |||
    fresh ["x","b","t0","t1"]
      (e === eabs x b &&& typ === arrow t0 t1 &&& call "typo" [cons x t0 env, b, t1]) |||
    fresh ["a","b","t0"]
      (e === eapp a b &&& call "typo" [env, a, arrow t0 typ] &&& call "typo" [env, b, t0])
  where
    [env,e,typ,a,x,b,t0,t1] = map V ["env","e","typ","a","x","b","t0","t1"]


env :: [Def]
env = [ lookupo, typo, disEqPeano, ltoDef, gtoDef]


unit_stlc1 :: IO ()
unit_stlc1 = do
  -- should give `id` as an answer
  runTest (topLevel 6) "stlc1" $ Program env $ fresh ["e"] (call "typo" [nil, V "e", arrow (tvar zero) (tvar zero)])
  -- should not give answer
  runTest (topLevel 6) "stlc2" $ Program env $ fresh ["e"] (call "typo" [nil, V "e", (tvar zero)])
  return ()

runTest function filename goal = do
  let path = printf "test/out/sym/%s" filename
  exists <- doesDirectoryExist path
  if exists
  then removeDirectoryRecursive path
  else return ()
  createDirectoryIfMissing True path

  tree <- function goal
  printTree (printf "%s/tree.dot" path) tree
  system (printf "dot -O -Tpng %s/*.dot" path)
  return ()
