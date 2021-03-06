module Test.Eval where

import           Test.Helper ((@?=))

import           Eval (Sigma, unify)
import           Syntax


unit_occursCheck = do
  unify (unify (Just ([] :: Sigma)) (V 0) (V 1)) (V 1) (C "constr" [V 0]) @?= Nothing
  unify (unify (unify (Just ([] :: Sigma)) (V 0) (V 1)) (V 1) (C "constr" [V 0])) (V 0) (V 1) @?= Nothing
