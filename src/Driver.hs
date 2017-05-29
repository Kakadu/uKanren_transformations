module Driver where
import MuKanren hiding (mplus)
import Control.Monad
import Debug.Trace
import Data.List (find, delete, partition)
import Data.Maybe (isJust, catMaybes)
import Data.Foldable (foldrM)

type GenRef = Int

data Tree subst ast = Success (subst,Int)
                    | Fail
                    | Step Int subst ast (Tree subst ast)
                    | Or Int subst ast (Tree subst ast) (Tree subst ast)
                    | Up Int subst ast
                    | Gen Int subst ast ESubst GenRef (Tree subst ast)
                    | Leaf (subst,Int) ast

data Ctx = EmptyCtx | ConjCtx AST Ctx deriving Show -- | Bot

instance (Show subst, Show ast) => Show (Tree subst ast) where
  show t = show' t 0 where
    nspaces n = [' ' | _ <- [1..n]]
    show' Fail n' = nspaces n' ++ "F\n"
    show' (Success (s,c)) n' = nspaces n' ++ "S " ++ show s ++ "\n"
    show' (Step n s a ch) n' = nspaces n' ++ "T " ++ show n ++ " " ++ show s ++ " " ++ show a ++ "\n" ++ show' ch (n+1)
    show' (Or n s a l r) n' = nspaces n' ++ "O " ++ show n ++ " " ++ show s ++ " " ++ show a ++ "\n" ++ show' l (n+1) ++ "\n" ++ show' r (n+1)
    show' (Up n s a) n' = nspaces n' ++ "U " ++ show n ++ " " ++ show s ++ " " ++ show a ++ "\n"
    show' (Gen n s a es gr ch) n' = nspaces n' ++ "G " ++ show gr ++ " " ++ show a ++ " " ++ show es ++ "\n" ++ show' ch (n+1)
    show' (Leaf s ast) n' = nspaces n' ++ "L " ++ show s ++ " " ++ show ast

rename t =
  let (t', _) = rename_ast t ([], 0) in t'
  where
    -- Fresh should be impossible at this stage
    rename_ast (Conj l r) s =
      let (l', s')  = rename_ast l s
          (r', s'') = rename_ast r s'
      in (Conj l' r', s'')
    rename_ast (Disj l r) s =
      let (l', s')  = rename_ast l s
          (r', s'') = rename_ast r s'
      in (Disj l' r', s'')
    rename_ast (Fun n a) s =
      let (a', s') = rename_ast a s
      in (Fun n a', s')
    rename_ast (Zzz a ) s =
      let (a', s') = rename_ast a s
      in (Zzz a', s')
    rename_ast (Call a args) s =
      let s' = s
          a' = a -- (a', s')    = rename_ast a s -- this loops. Doesn't seem necessary for now anyway
          (arg', s'') = foldl (\(xs, s) x -> let (x', s') = rename_t x s in (x' : xs, s'))
                              ([], s')
                                args
      in (Call a' $ reverse arg', s'')
    rename_ast (Uni l r ) s =
      let (l', s')  = rename_t l s
          (r', s'') = rename_t r s'
      in (Uni l' r', s'')
    rename_ast x s = (x, s)

    rename_t (Var v) s@(m, c) =
      case lookup v m of
        Nothing -> let v' = Var c in (v', ((v, v') : m, c+1))
        Just v' -> (v', s)
    rename_t (Pair l r) s =
      let (l', s')  = rename_t l s
          (r', s'') = rename_t r s'
      in (Pair l' r', s'')
    rename_t x s = (x, s)

renaming l r = rename l == rename r

instance Eq AST where
  Conj l l' == Conj r r' = l == r && l' == r'
  Disj l l' == Disj r r' = l == r && l' == r'
  Uni  l l' == Uni  r r' = l == r && l' == r'
  Zzz l     == Zzz r     = l == r
  Call (Fun l _) ls == Call (Fun r _) rs = l == r && foldl (\acc (l, r) -> acc && l == r) True (zip ls rs)
  _ == _ = False

isCoupling l r =
  case (l,r) of
    (Uni  _ _, Uni  _ _) -> True
    (Conj _ _, Conj _ _) -> True
    (Disj _ _, Disj _ _) -> True
    (Call _ _, Call _ _) -> True
    (Zzz    _, Zzz    _) -> True
    _ -> False

embed l r =
  let
      embedT :: Term -> Term -> [(Var, Var)] -> Maybe [(Var, Var)]
      embedT l r ren = coupleT l r ren `mplus` diveT l r ren

      coupleT l r renaming =
        case (l,r) of
          -- terms should be embedded up to renaming
          (Var l, Var r) -> if l `elem` fst (unzip renaming)
                            then if (l,r) `elem` renaming then Just renaming else Nothing
                            else Just ((l,r):renaming)

          (Nil, Nil) -> Just renaming
          (Pair l l', Pair r r') -> embedT l r renaming >>= embedT l' r'
          (Atom l, Atom r) | l == r -> Just renaming
          _ -> Nothing

      diveT l r renaming =
        case (l,r) of
        (_, Var _) -> Nothing
        (_, Atom _) -> Nothing
        (_, Nil) -> Nothing
        (x, Pair l r) -> -- trace ("Checking terminals diving. X: " ++ show x ++ " AND pair: " ++ show (pair l r)) $
                         embedT x l renaming `mplus` embedT x r renaming
        _ -> Nothing

      embed' l r renaming = couple l r renaming `mplus` dive l r renaming

      couple l r renaming =
        case (l,r) of
          (Uni  l l', Uni  r r') -> embedT l r renaming >>= embedT l' r'
          (Conj l l', Conj r r') -> embed' l r renaming >>= embed' l' r'
          (Disj l l', Disj r r') -> embed' l r renaming >>= embed' l' r'
          (Call (Fun nl al) als, Call (Fun nr ar) ars) | nl == nr ->
            -- trace ("call function embedding: " ++ show (zip als ars) ) $
            foldrM (\(l,r) ren ->
              -- trace ("args renaming check. l: " ++ show l ++ " AND r: " ++ show r ++ " Renaming: " ++ show ren ) $
              embedT l r ren) renaming (zip als ars)
          (Zzz l, Zzz r) -> embed' l r renaming
          _ -> Nothing

      dive l r renaming =
        case (l,r) of
          (_, Uni _ _) -> Nothing
          (l, Zzz r) -> embed' l r renaming
          (l, Conj r r') -> embed' l r renaming `mplus` embed' l r' renaming
          _ -> Nothing
  in
    -- trace ("checking for embedding: l: " ++ show l ++ " AND r: " ++ show r ) $
    isJust $ embed' l r []

--unfold _ Nothing = [(Nothing, Nothing)]
--
--unfold x st@(Just st'@(s,c)) =
----  if c >= 6 then [(Nothing, Nothing)] else
--  case x of
--    GV _ _ _ -> [(Nothing, st)]
--    Uni  l r -> [(Nothing, unify l r s >>= \s -> Just (s,c))]
--    Disj (GV _ _ _) r -> [(Just r, st)]
--    Disj l (GV _ _ _) -> [(Just l, st)]
--    Disj l r -> unfold l st ++ unfold r st
--    Fresh f  -> [(Just $ f (var c), Just (s,c+1))]
--    Zzz a    -> [(Just a,st)]
--    Fun _ a  -> [(Just a,st)]
--    Call (Fun _ a) arg -> [(Just a,st)]
--    Conj (GV _ _ _) r -> [(Just r, st)]
--    Conj l (GV _ _ _) -> [(Just l, st)]
--    Conj (Uni l l') (Uni r r') -> [(Nothing, unify l l' s >>= \s -> unify r r' s >>= \s -> Just (s,c))]
--    Conj (Uni l l') r -> unfold r (unify l l' s >>= \s -> Just (s,c))
--    Conj l (Uni r r') -> unfold l (unify r r' s >>= \s -> Just (s,c))
--    Conj l r -> let l' = unfold l st
--                in concatMap (\y -> case y of
--                                     (Nothing, Nothing) -> [y]
--                                     (Nothing, st@(Just _)) -> unfold r st
--                                     (Just x', st@(Just _)) -> [(Just $ Conj x' r, st)]
--                                     _ -> error "invalid substitution during unfolding")
--                             l'

generalize :: AST -> AST -> Int -> Int -> (AST, ESubst, ESubst, Int)
generalize smaller bigger n up =
  let generalizeT :: Term -> Term -> ESubst -> ESubst -> Int -> (Term, ESubst, ESubst, Int)
      generalizeT l r s1 s2 n =
        case (l,r) of
          (Pair l r, Pair l' r') ->
            let (l'', s1' , s2' , n' ) = generalizeT l l' s1  s2  n
                (r'', s1'', s2'', n'') = generalizeT r r' s1' s2' n'
            in (Pair l'' r'', s1'', s2'', n'')
          (Var v, Var u) | v == u -> (Var v, s1, s2, n)  -- TODO
          (Var _, Var _) ->
            (Var n, (n, Right r) : s1, (n, Right l) : s2, n+1)
          (Var _, Pair _ _) ->
            (Var n, (n, Right r) : s1, (n, Right l) : s2, n+1)
          (Atom _, Atom _) -> -- TODO why ignoring the actual values?
            (l, s1, s2, n)
          (Nil, Nil) ->
            (l, s1, s2, n)
          (x, p@(Pair _ _)) ->
            (Var n, (n, Right p) : s1, (n, Right x) : s2, n+1)
          _ -> error $ "Failed to generalize the following terms:\n" ++ show l ++ "\n" ++ show r ++ "\nThis is impossible due to embedding defenition"

      generalize' :: AST -> AST -> ESubst -> ESubst -> Int -> Int -> (AST, ESubst, ESubst, Int)
      generalize' smaller bigger s1 s2 n up =
        case (smaller, bigger) of
          (Disj l r, Disj l' r') ->
            let (l'', s1', s2', n') = generalize' l l' s1 s2 n up
                (r'', s1'', s2'', n'') = generalize' r r' s1' s2' n' up
            in (Disj l'' r'', s1'', s2'', n'')
          (Conj l r, Conj l' r') ->
            let (l'', s1', s2', n') = generalize' l l' s1 s2 n up
                (r'', s1'', s2'', n'') = generalize' r r' s1' s2' n' up
            in (Conj l'' r'', s1'', s2'', n'')
          (Zzz s, Zzz b) ->
            let (g, s1', s2', n') = generalize' s b s1 s2 n up
            in (Zzz g, s1', s2', n')
          (Call (Fun ns as) args, Call (Fun nb ab) argb) | ns == nb ->
            let (arg', s1', s2', n') = foldr (\(l, r) (prev, s1, s2, n) ->
                                               let (cur, s1', s2', n') = generalizeT l r s1 s2 n
                                               in (cur : prev, s1', s2', n')
                                             )
                                             ([], s1, s2, n)
                                             (zip args argb)
            in (Call (Fun ns as) arg', s1', s2', n')
          (Uni l r, Uni l' r') ->
            let (l'', s1', s2', n') = generalizeT l l' s1 s2 n
                (r'', s1'', s2'', n'') = generalizeT r r' s1' s2' n'
            in (Uni l'' r'', s1'', s2'', n'')
          (s, b) ->
            case find (\(x,t) -> t == Left s && lookup x s2 == Just (Left b)) s1 of
              Just (x,t) -> (GV x s1 up, s1, s2, n)
              Nothing -> let nv = n+1
                         in
                            (GV nv ((nv, Left b) : s1) up, (nv, Left b) : s1, (nv, Left s) : s2, nv)
  in generalize' smaller bigger [] [] n up

flatten t EmptyCtx = t
--flatten t Bot = t
flatten t (ConjCtx t' ctx) = flatten (Conj t t') ctx

unify' l r st@(s,c) =
  unify l r s >>= \s -> Just (s,c)


uniToTheTop t =
  let (u, r) = extractUni t in conj (u ++ [conj r])
  where extractUni t = partition (\x -> case x of { Uni _ _ -> True ; _ -> False }) (listifyConj t)
        listifyConj (Conj l r) = listifyConj l ++ listifyConj r
        listifyConj t = [t]

applySubst (Conj l r)    s        = Conj (applySubst l s) (applySubst r s)
applySubst (Disj l r)    s        = Disj (applySubst l s) (applySubst r s)
applySubst t@(Fresh f)   (s,c)    = t -- applySubst (f $ var c) (s,c+1)
applySubst (Fun n a)     s        = Fun n $ applySubst a s
applySubst (Zzz a)       s        = Zzz $ applySubst a s
applySubst (Call a args) s'@(s,c) = Call (applySubst a s') (map (`walk'` s) args)
applySubst (Uni l r)     (s,c)    = Uni (walk' l s) (walk' r s)
applySubst g@(GV _ _ _)   _       = g

unf (Uni l r) EmptyCtx st =
      case unify' l r st of
        Just st' -> Success st'
        Nothing -> Fail

unf t@(Uni l r) c@(ConjCtx a ctx) st =
  case unify' l r st of
    Just st'@(s',c') -> unf a ctx st'
    Nothing -> Fail

unf t@(Zzz a) ctx st@(s,c) = unf a ctx st
unf t@(Disj l r) ctx st@(s,c) = Or 0 s t (unf l ctx st) (unf r ctx st)
unf t@(Conj l r) ctx st@(s,c) = unf l (ConjCtx r ctx) st
unf t@(Fresh f) ctx st@(s,c) = unf (f $ var c) ctx (s,c+1)
unf t@(Call (Fun _ funb) args) ctx st@(s,c) = Leaf st (flatten t ctx)
unf t@(GV v es r) EmptyCtx st@(s,c) = error "generalized variable" -- Up r s t
unf t@(GV v es r) c@(ConjCtx a ctx) st@(s,_) = error "generalized variable" -- Gen 0 s t es r (unf a ctx st)
unf (Fun _ _) _ _ = error "unapplied function"
unf t ctx st = error ("wow " ++ show t)

getLeaves (Or _ _ _ l r) = getLeaves l ++ getLeaves r
getLeaves Fail = []
getLeaves x = [x]

unfold t st =
  case t of
    Call (Fun n b) args -> getLeaves $ unf b EmptyCtx st
    t -> getLeaves $ unf t EmptyCtx st

unfoldDet orig st@(s,c) =
  let tree =
        case orig of
          Call (Fun n b) args -> unf b EmptyCtx st
          t -> unf t EmptyCtx st
  in getUnfold tree
  where
    getUnfold tree =
      case getLeaves tree of
        [] -> (Nothing, Nothing)
        (x:y:xs) -> (Just orig, Just st)
        [Success s] -> (Nothing, Just s)
        [Leaf s a] -> (Just a, Just s)


drive ast =
  drive' 0 ast EmptyCtx EmptyCtx emptyState []
  where
    drive' _ (Uni l r) EmptyCtx lctx st _ =
      case unify' l r st of
        Just st' -> Success st'
        Nothing -> Fail
--
--    drive' _ (Uni l r) Bot lctx st _ =
--      case unify' l r st of
--        Just st' -> Success st'
--        Nothing -> Fail


    drive' n t@(Uni l r) c@(ConjCtx a ctx) lctx st ancs =
      case unify' l r st of
        Just st'@(s',c') ->
          let anc =
                    flatten t c
--                    applySubst (flatten t c) st'
          in Step n s' anc (drive' (n+1) a ctx lctx st' ((anc,n):ancs))
        Nothing -> Fail

    drive' n t@(Zzz a) ctx lctx st@(s,c) ancs =
      let anc =
                flatten t ctx
--                applySubst (flatten t ctx) st
      in Step n s anc (drive' (n+1) a ctx lctx st ((anc,n):ancs))

    drive' n t@(Disj l r) ctx lctx st@(s,c) ancs =
      let anc =
                flatten t ctx
--                applySubst (flatten t ctx) st
      in Or n s anc (drive' (n+1) l ctx lctx st ((anc,n):ancs)) (drive' (n+1) r ctx lctx st ((anc,n):ancs))

    drive' n t@(Conj l r) ctx lctx st@(s,c) ancs =
      let anc =
                flatten t ctx
--                applySubst (flatten t ctx) st
      in Step n s anc (drive' (n+1) l (ConjCtx r ctx) lctx st ancs)

    drive' n t@(Fresh f) ctx lctx st@(s,c) ancs =
      let anc =
                flatten t ctx
--                applySubst (flatten t ctx) st
      in Step n s anc (drive' (n+1) (f $ var c) ctx lctx (s,c+1) ancs)

    drive' _ (Fun _ _) _ _ _ _ = error "unapplied function"

    drive' n_anc t@(Call (Fun _ funb) args) ctx lctx st@(s,c) ancs =
      --if n_anc >= 10 then Fail else
      let t' = flatten t ctx
          ctxToList (ConjCtx l ctx) = l : ctxToList ctx
          ctxToList _ = []
          anc = conj $ reverse  (ctxToList lctx) ++ [t']
          first = let unfolded = unfold t st in {- trace ("unfolding first " ++ show t ++ " " ++ show unfolded ) $ -} unfolded

          throughCtx' subst ctx =
            let (l, subst') = throughCtx subst ctx
            in
              -- trace ("subst: " ++ show subst ++ " into ctx: " ++ show ctx) $
              (case catMaybes l of {[] -> Nothing; x -> Just $ conj x}, subst')
            where
              throughCtx subst (EmptyCtx) = ([Nothing], Just subst)
              throughCtx subst (ConjCtx ast ctx) =
                case unfoldDet ast subst of
                  (Nothing, Nothing) -> ([Nothing], Nothing)
                  (Nothing, Just subst') -> throughCtx subst' ctx
                  (Just ast', Just subst') -> let (ast'', subst'') = throughCtx subst' ctx in (Just ast' : ast'', subst'')
                  _ -> error "something strange happended during unfolding"

          simplify blah =
            let result = simplify' blah in {- trace ("simplified: " ++ show result) -} result
            where
              simplify' (Success subst) =
                throughCtx' subst ctx
              simplify' (Leaf subst ast) =
                let (ast', subst') = throughCtx' subst ctx
                in  case ast' of
                      Nothing -> (Just ast, subst')
                      Just ast'' -> (Just $ Conj ast ast'', subst')
          makeNode (Nothing,Nothing) n = Fail
          makeNode (Nothing, Just subst) n = Success subst
          makeNode (Just ast, Just subst@(s',c')) n =
            -- trace ("making node from ast: " ++ show ast ++ "\nwith subst" ++ show subst) $
            case find (\(a,n') -> renaming a ast) ((anc,n_anc):ancs) of
              Just (a,n') ->  {- trace (show ast) $ -} Up n' s' ast
              Nothing ->
                case find (\(a,n') -> isCoupling a ast && embed a ast) ((anc,n_anc):ancs) of
                     Just (a,n') ->
                       let qwert@(g, s1, s2, c'') = -- trace ("Generalizing\na:   " ++ show a ++ "\nast: " ++ show ast) $
                                                    generalize a ast c' n'
                       in -- TODO think of better solution!
                         case find (\(a,n') -> renaming a g) ((anc,n_anc):ancs) of
                           Nothing -> -- trace (show qwert) $
                                      drive' (n+1) g EmptyCtx lctx (s',c'') ((anc,n_anc):ancs)
                           Just (a,n') -> Up n' s' g
                     Nothing -> drive' n ast EmptyCtx EmptyCtx subst ((anc,n_anc):ancs)


          nodes [] n = Fail
          nodes [x] n = makeNode (simplify x) (n+1)
          nodes (x:xs) n = Or (n+1) s anc (makeNode (simplify x) (n+2)) (nodes xs (n+1))
          ch = {- trace ("ctx: " ++ show ctx ++ "\nunfolded " ++ show first ++ "\n") $ -} nodes first n_anc
      in

        Step n_anc s anc ch

--    drive' n t@(Call (Fun _ funb) args) ctx lctx st@(s,c) ancs =
----      if n >= 100 then Fail else
--      let t' = flatten t ctx
--          anc =
--            let ctxToList (ConjCtx l ctx) = l : ctxToList ctx
--                ctxToList _ = []
--                help ctx = conj $ reverse  (ctxToList ctx) ++ [t']
--            in
--               help lctx
----               applySubst (help lctx) st
--          ch =
--               case find (\(a,n') -> renaming a anc) ancs of
--                 Just (a,n') ->
--                   case ctx of
--                     Bot -> Up n' s anc
--                     EmptyCtx ->  drive' (n+1) funb Bot lctx st (ancs)
--                                 -- Up n' s anc
--                     ConjCtx next ctx' -> let nv = c+1
--                                              es = [(nv, Left t)]
--                                              generalizedish = flatten (GV nv es n) ctx
--                                          in Gen (n+1) s generalizedish es n (drive' (n+2) next ctx' (ConjCtx t lctx) (s,nv) (ancs))
--                 Nothing ->
--                   case find (\(a,n') -> isCoupling a anc && embed a anc) ancs of
--                     Just (a,n') ->
--                       case ctx of
--                         Bot ->
--                                let (g, s1, s2, c') = generalize a anc c n'
--                                in drive' (n+1) g EmptyCtx lctx st ((anc,n):ancs)
--                         EmptyCtx ->
--                                     drive' (n+1) funb Bot lctx st ancs
----                                     let (g, s1, s2, c') = generalize a anc c n'
----                                     in drive' (n+1) g EmptyCtx lctx st ((anc,n):ancs)
--                         ConjCtx next ctx' ->
--                           let nv = c+1
--                               es = [(nv, Left t)]
--                               generalizedish = flatten (GV nv es n) ctx
--                           in Gen (n+1) s generalizedish es n (drive' (n+2) next ctx' (ConjCtx t lctx) (s,nv) (ancs))
--                     Nothing -> drive' (n+1) funb ctx lctx st ((anc,n):ancs)
--      in Step n s anc ch

    drive' n t@(GV v es r) EmptyCtx lctx st@(s,c) ancs =
      Up r s t

--    drive' n t@(GV v es r) Bot lctx st@(s,c) ancs =
--      Up r s t


    drive' n t@(GV v es r) c@(ConjCtx a ctx) lctx st@(s,_) ancs =
     let anc =
               flatten t c
--               applySubst (flatten t c) st
     in Gen n s anc es r (drive' (n+1) a ctx lctx st ((anc,n):ancs))