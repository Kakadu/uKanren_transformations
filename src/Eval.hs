{-# LANGUAGE TupleSections #-}
module Eval where

import Control.Monad
import Data.List
import Data.Maybe 
import Syntax
import Stream

-- States
type Iota  = X -> Ts
type Sigma = [(S, Ts)]
type Delta = [S]
type P     = String -> Def
type Gamma = (P, Iota, Delta)

-- Unification
unify :: Maybe Sigma -> Ts -> Ts -> Maybe Sigma 
unify Nothing _ _ = Nothing
unify st@(Just subst) u v = 
  unify' (walk u subst) (walk v subst)  where
    unify' (V u) (V v) | u == v = Just subst
    unify' (V u) _              = Just $ (u, v) : subst
    unify' _ (V v)              = Just $ (v, u) : subst
    unify' (C a as) (C b bs) | a == b && length as == length bs = 
      foldl (\ st (u, v) -> unify st u v) st $ zip as bs
    unify' _ _ = Nothing
    walk x@(V v) s =
      case lookup v s of
        Nothing -> x
        Just t  -> walk t s
    walk u     _ = u

-- Syntactic terms -> semantic terms

---- Interpreting syntactic variables 
infix 9 <@>
(<@>) :: Iota -> Tx -> Ts
i <@> (V x)    = i x
i <@> (C c ts) = C c $ map (i<@>) ts

---- Extending variable interpretation
extend :: Iota -> X -> Ts -> Iota
extend i x ts y = if x == y then ts else i y 

---- Applying substitution
substitute :: Sigma -> Ts -> Ts
substitute s t@(V x)  = case lookup x s of Nothing -> t ; Just tx -> substitute s tx
substitute s (C m ts) = C m $ map (substitute s) ts

-- Pre-evaluation
pre_eval :: Gamma -> G X -> (G S, Gamma)
pre_eval g@(_, i, _) (t1 :=: t2)   = (i <@> t1 :=: i <@> t2, g)
pre_eval g           (g1 :/\: g2)  = let (g1', g' ) = pre_eval g  g1 in
                                     let (g2', g'') = pre_eval g' g2 in
                                     (g1' :/\: g2', g'')
pre_eval g           (g1 :\/: g2)  = let (g1', g' ) = pre_eval g  g1 in
                                     let (g2', g'') = pre_eval g' g2 in
                                     (g1' :\/: g2', g'')
pre_eval g@(p, i, d) (Fresh x g')  = pre_eval (p, extend i x (V y), d') g' where y : d' = d 
pre_eval g@(_, i, _) (Invoke f fs) = (Invoke f (map (i <@>) fs), g)
 
-- Evaluation relation
eval :: Gamma -> Sigma -> G S -> Stream (Sigma, Delta)
eval     (p, i, d) s (t1 :=:  t2)  = fmap (,d) (maybeToStream $ unify (Just s) t1 t2)
eval env           s (g1 :\/: g2)  = eval env s g1 `mplus` eval env s g2
eval env@(p, i, d) s (g1 :/\: g2)  = eval env s g1 >>= (\ (s', d') -> eval (p, i, d') s' g2)
eval env@(p, i, d) s (Invoke f as) = 
  let (_, fs, g) = p f in
  let i'         = foldl (\ i' (f, a) -> extend i' f $ a) i $ zip fs as in
  let (g', env') = pre_eval (p, i', d) g in
  eval env' s g'

env0 :: P -> Gamma
env0 p = (p, (\_ -> undefined), [0..]) 

s0 :: Sigma
s0 = []

run :: Spec -> Stream Sigma
run (defs, goal) =
  let p n = fromJust $ find (\ (m, _, _) -> m == n) defs in
  let (goal', env') = pre_eval (env0 p) goal in
  fmap fst $ eval env' s0 goal'
