{-# LANGUAGE PackageImports #-}

module Prelude where

import "base" Prelude (Bool (..), return, (+), (-))

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
    1 -> True
    _ -> even (x - 1)
