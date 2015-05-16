{-# LANGUAGE PackageImports #-}

module Prelude where

import "base" Prelude (Bool (..), return, (+), (-))

------------------------
-- Constructor functions

cons a b = a : b

nil = []

map f l =
  case l of
    [] -> []
    (:) h t -> (:) (f h) (map f t)

filter p l =
  case l of
    [] -> []
    h : t -> if p h then h : (filter p t)
                    else filter p t

foldl f i l =
  case l of
    [] -> i
    h : t -> foldl f (f i h) t

foldr f i l =
  case l of
    [] -> i
    h : t -> f h (foldr f i t)

someFun a b =
  case a of
    1 -> 0
    _ -> a + b

sum l = foldr (\a b -> a + b) 0 l

sum' l =
  case l of
    [] -> 0
    a : b -> a + sum' b

sum'' acc l =
  case l of
    [] -> acc
    a : b -> sum'' (acc + a) b

someList = [1, 2, 3]

even x =
  case x of
    0 -> True
    _ -> odd (x - 1)

odd x =
  case x of
    0 -> False
    1 -> True
    _ -> even (x - 1)

length x =
  case x of
    [] -> 0
    _a : rest -> 1 + length rest

span p l =
  case l of
    [] -> ([], [])
    x : xs ->
      if p x
        then
         case span p xs of
           (p, r) -> (x : p, r)
        else ([], l)

append l1 l2 =
  case l1 of
    [] -> l2
    x : xs -> x : append xs l2

reverse l =
  case l of
    [] -> []
    x : xs -> append (reverse xs) [x]

example = span odd [1,2,3]
