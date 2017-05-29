module Main where
import MuKanren
import Driver
import Debug.Trace
import Programs


run k a =
  let
      take k (Immature s) | k > 0 = take k s
      take k (Mature h t) | k > 0 = Mature h $ take (k-1) t
      take k _ = Empty
  in take k $ eval a emptyState

main =
  do
    print $ drive (callFresh (\xs -> callFresh (\ys -> callFresh (\zs -> call (appendo xs ys zs) [xs, ys, zs]))))

--    print $ unfoldDet (call (appendo (Var 0) (Var 1) (Var 2)) [Var 0, Var 1, Var 2] )
--                      ([], 3)
--
--    print $ unfold (call (appendo (Var 0) (Var 1) (Var 2)) [Var 0, Var 1, Var 2] )
--                   ([], 3)


    print $ drive (callFresh (\x ->
                    callFresh (\y ->
                    callFresh (\i ->
                    callFresh (\z ->
                    callFresh (\r ->
                    call (appendo x y i) [x, y, i] &&& call (appendo i z r) [i,z,r]))))))

    print $ drive (callFresh (\xs -> callFresh (\sx -> call (reverso xs sx) [xs, sx])))

--    Doesn't terminate
--    print $ drive (callFresh (\xs -> callFresh (\sx -> call (revAcco xs nil sx) [xs, nil, sx])))


