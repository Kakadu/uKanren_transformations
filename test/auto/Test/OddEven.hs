{-# LANGUAGE NoImplicitPrelude #-}

-- Use command `stack test --ta '-p "oddEven"'` to test only that file

module Test.OddEven where

import           Prelude hiding (succ,odd,even)
import           SymbolicExecution (topLevel)
import           Printer.Dot
import           Printer.SymTree ()
import           Syntax
import           System.Directory
import           System.Process   (system)
import           Text.Printf

-- dA = Program doubleAppendo $ fresh ["x", "y", "z", "r"] (call "doubleAppendo" [V "x", V "y", V "z", V "r"])
-- revAcco' = Program revAcco $ fresh ["x", "y"] (call "revacco" [V "x", nil, V "y"])
-- rev = Program reverso $ fresh ["x", "y"] (call "reverso" [V "x", V "y"])

zero :: Term a
zero = C "O" []

succ :: Term a -> Term a
succ x = C "S" [x]

even :: Def
even =
  Def "even" ["x"] $
    (x === zero) |||
    fresh ["x2"] (x === succ x2 &&& call "odd" [x2])
  where
    [x, x2] = map V ["x", "x2"]

odd :: Def
odd =
  Def "odd" ["x"] $
    (x === succ zero) |||
    fresh ["x2"] (x === succ x2 &&& call "even" [x2])
  where
    [x, x2] = map V ["x", "x2"]

oddAndEven :: [Def]
oddAndEven =
  [ Def "oddAndEven" ["x"] $
      (call "odd" [x] &&& call "even" [x])
  , odd
  , even
  ]
  where
    [x] = map V ["x"]


unit_oddEven :: IO ()
unit_oddEven = do
  -- runTest (topLevel 5) "da" dA
  -- runTest (topLevel 5) "rev" rev
  -- runTest (topLevel 5) "even" $ Program oddAndEven $ fresh ["x"] (call "even" [V "x"])
  -- runTest (topLevel 5) "odd"  $ Program oddAndEven $ fresh ["x"] (call "odd"  [V "x"])
  runTest (topLevel 5) "oddAndEven" $ Program oddAndEven $ fresh ["x"] (call "oddAndEven" [V "x"])
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
  system (printf "dot -O -Tpdf %s/*.dot" path)
  return ()
