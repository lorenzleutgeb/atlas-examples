and :: Tree Bool -> Bool
and t =
  match t with
    | nil -> true
    | (l, x, r) ->
      if and l
        then if x then and r
                  else false
        else false;

or :: Tree Bool -> Bool
or t =
  match t with
    | nil -> false
    | (l, x, r) ->
      if or l then true
              else if x then true
                        else or r;

any :: (a -> Bool) * Tree a -> Bool
any f t = or (map f t);

all :: (a -> Bool) * Tree a -> Bool
all f t = and (map f t);

map :: (a -> b) * Tree a -> Tree b
map f t =
  match t with
    | nil       -> nil
    | (l, x, r) -> (map f l, f x, map f r);

fold :: (b * a -> b) * b * Tree a -> b
fold f z t =
  match t with
    | nil -> z
    | (l, x, r) -> f (f (fold f z l) x) (fold f z t);

zipWith :: (a * b -> c) * Tree a * Tree b -> Tree c
zipWith f t u =
  match t with
    | nil       -> nil
    | (l, x, r) ->
        match u with
          | nil       -> nil
          | (v, y, w) -> let l' = zipWith f l v in
                         let r' = zipWith f r w in
                         (l', f x y, r');
