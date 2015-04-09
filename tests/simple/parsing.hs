import Prelude ((+), return)

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

someList = [1, 2, 3]

main = return ()
