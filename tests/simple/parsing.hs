map f l =
  case l of
    [] -> []
    (:) h t -> (:) (f h) (map f t)

someFun a b =
  case a of
    1 -> 0
    _ -> (+) a b

someList = [1, 2, 3]
