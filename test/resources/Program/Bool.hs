module Program.Bool where

import Syntax

falso :: Term a
falso = C "false" []

trueo :: Term a
trueo = C "true"  []

nandoDef :: Def 
nandoDef = 
    ( Def "nando" ["a", "b", "c"]
        (
          ( a === falso &&& b === falso &&& c === trueo ) |||
          ( a === falso &&& b === trueo &&& c === trueo ) |||
          ( a === trueo &&& b === falso &&& c === trueo ) |||
          ( a === trueo &&& b === trueo &&& c === falso )
        )
    )
  where 
    [a, b, c] = map V ["a", "b", "c"]

nando :: [Def] 
nando = [nandoDef]

notoDef :: Def 
notoDef =
    ( Def "noto" ["a", "na"] 
      ( 
        call "nando" [a, a, na] 
      ) 
    ) 
  where 
    [a, na] = map V ["a", "na"]

noto :: [Def]
noto = notoDef : nando

oroDef :: Def
oroDef =
    ( Def "oro" ["a", "b", "c"]
        (
          fresh ["aa", "bb"]
            (
              call "nando" [a, a, aa] &&&
              call "nando" [b, b, bb] &&&
              call "nando" [aa, bb, c]
            )
        )
    ) 
  where 
    [a, b, c, aa, bb] = map V ["a", "b", "c", "aa", "bb"]

oro :: [Def]
oro = oroDef : nando

andoDef :: Def
andoDef =
    ( Def "ando" ["a", "b", "c"] 
      (
        fresh ["ab"] 
        (
          call "nando" [a, b, ab] &&&
          call "nando" [ab, ab, c]
        )
      )
    )
  where 
    [a, b, c, ab] = map V ["a", "b", "c", "ab"]

ando :: [Def]
ando = andoDef : nando 

bool :: Term t -> String
bool (C "false" []) = "false"
bool (C "true"  []) = "true"
bool _ = "?!"