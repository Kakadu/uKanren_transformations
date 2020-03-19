{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module SymbolicExecution where

import qualified CPD.LocalControl   as LC
import           Data.Foldable      (foldlM)
import           Data.List          (find, intersect, partition, (\\))
import qualified Data.Map.Strict    as M
import           Data.Maybe         (mapMaybe, fromMaybe)
import           Debug.Trace        (trace)
import           Control.Exception  (assert)
import           Embed
import qualified Eval               as E
import           Generalization     (generalizeGoals, generalizeSplit)
import           Prelude            hiding (or)
import           Syntax
import           Text.Printf        (printf)
import           Util.Miscellaneous (fst3, show')

data SymTree = Fail
             | Success E.Sigma
             | Disj [SymTree] [G S] E.Sigma
             | Conj [SymTree] [G S] E.Sigma
             | Prune [G S] E.Sigma
             deriving (Show, Eq)

data WhistleInfo = NoAnswers | HasAnswers

evalTree root = helper [] root
  where
    helper _ Fail = NoAnswers
    helper _ (Prune _ _)   = HasAnswers
    helper _ (Success _)   = HasAnswers
    helper path (Conj [t] [g] _) | whistles g path = NoAnswers
    helper path (Conj [t] [g] _)                   = helper (g:path) t

    helper path (Disj ts  gs _)  =
      assert (length ts == length gs) $
      foldl (\case HasAnswers -> const HasAnswers; _ -> id) NoAnswers $
      zipWith (\t g -> if whistles g path then NoAnswers else helper (g:path) t) ts gs
    whistles goal path = False



topLevel :: Int -> Program -> SymTree
topLevel depth (Program defs goal) =
    let gamma = E.updateDefsInGamma E.env0 defs in
    let (logicGoal, gamma', _) = E.preEval gamma goal in
    go logicGoal [] gamma' E.s0 depth
  where
    go :: G S -> [G S] -> E.Gamma -> E.Sigma -> Int -> SymTree
    go goal ctx _ state d | d <= 1 = Prune (goal : ctx) state
    go goal ctx env state depth =
      let (unified, gamma) = oneStep goal env state in
      Disj (map (\case
                   ([],       s') -> leaf s'
                   (g@(h:tl), s') -> Conj [go h tl gamma s' (depth - 1)] g s'
                )
                ((\(g, s) -> (ctx++g, s)) <$> unified))
            (goal : ctx)
            state

type DNF = [([G S], E.Sigma)]

oneStep :: G S -> E.Gamma -> E.Sigma -> (DNF, E.Gamma)
oneStep goal env state =
    let (unfolded, gamma) = LC.oneStepUnfold goal env in
    let normalized = LC.normalize unfolded in
    let unified = mapMaybe (LC.unifyStuff state) normalized in
    (unified, gamma)

leaf :: E.Sigma -> SymTree
leaf [] = Fail
leaf s  = Success s

simplify :: SymTree -> SymTree
simplify =
    go
  where
    go (Disj ch g s) = failOr   ch (\x -> Disj x g s)
    go (Conj ch g s) = failConj ch (\x -> Conj x g s)
    go x = x
    failOr ch f =
      let simplified = filter (/= Fail) $ map go ch in
      if null simplified
      then Fail
      else f simplified
    failConj ch f =
      let simplified = map go ch in
      if Fail `elem` simplified
      then Fail
      else f simplified
