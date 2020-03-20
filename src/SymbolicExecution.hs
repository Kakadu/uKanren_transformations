{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unused-imports -fwarn-incomplete-patterns #-}

module SymbolicExecution where

import qualified CPD.LocalControl   as LC
import           Data.Foldable      (foldlM, or)
import           Data.List          (find, intersect, partition, (\\))
import qualified Data.Map.Strict    as M
import           Data.Maybe         (mapMaybe, fromMaybe, isJust)
import           Debug.Trace        (trace)
import           Control.Exception  (assert)
import           Control.Monad      (zipWithM)
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
    helper _ Fail          = return NoAnswers
    helper _ (Prune _ _)   = return HasAnswers
    helper _ (Success _)   = return HasAnswers
    -- helper path (Conj [t] [g] _) | whistles g path = return NoAnswers
    -- helper path (Conj [t] [g] _)                   = helper (g:path) t
    helper path root@(Conj ts  gs _) = hack path root ts gs
    helper path root@(Disj ts  gs _) =
      assert (length ts == length gs) $
      hack path root ts gs

    hack path root ts gs = do
      info <- zipWithM f ts gs
      ans <- return $ foldl (\case HasAnswers -> const HasAnswers; _ -> id) NoAnswers info
      () <- case ans of
          HasAnswers -> return ()
          NoAnswers -> printf "found node without answers: %s\n" (show gs)
      return ans
        where
          f t g = if whistles g path then return NoAnswers else helper (g:path) t

    whistles :: G S -> [G S] -> Bool
    whistles goal path =
      or $ map (whistles1 goal) path
    whistles1 (Invoke name1 _) (Invoke name2 _) | name1 /= name2 = False
    whistles1 (Invoke name1 xs) (Invoke name2 ys) =
      isJust $ foldl (>>=) (Just []) $ zipWith more_general xs ys

    whistles1 _ _ = error "should not happen"

    more_general :: Term S -> Term S -> [(S, Term S)] -> Maybe  [(S, Term S)]
    more_general  (V v) b subst =
      case lookup v subst of
        Just x -> more_general x b subst
        Nothing -> Just ((v,b) : subst)
    more_general (C s _)  (C s2 _) _ | s /= s2 = Nothing
    more_general (C _ xs) (C _ ys) _ | length xs /= length ys = Nothing
    more_general (C _ xs) (C _ ys) subst =
      foldl (\acc (x,y) -> acc >>= more_general x y) (Just subst) $ zip xs ys
    more_general (C _ _) (V _) _ = Nothing


topLevel :: Int -> Program -> IO SymTree
topLevel depth (Program defs goal) =
    let gamma = E.updateDefsInGamma E.env0 defs in
    let (logicGoal, gamma', _) = E.preEval gamma goal in
    do
      tree <- go logicGoal [] gamma' E.s0 depth
      evalTree tree
      return tree
  where
    go :: G S -> [G S] -> E.Gamma -> E.Sigma -> Int -> IO SymTree
    go goal ctx _ state d | d <= 1 = return $ Prune (goal : ctx) state
    go goal ctx env state depth = do
        let (unified, gamma) = oneStep goal env state
        disjs <- mapM  (\case
                        ([],       s') -> return $ leaf s'
                        (g@(h:tl), s') -> go h tl gamma s' (depth - 1) >>= \h -> return $ Conj [h] g s'
                      )
                      ((\(g, s) -> (ctx++g, s)) <$> unified)

        return $ Disj disjs (goal : ctx) state

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
