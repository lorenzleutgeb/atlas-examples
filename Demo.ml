f ::  Tree a * a *  Tree a ->  Tree a;
f l x r = (l, x, r);

g :: Tree a * Tree a -> Tree a
g t e1 =
  match t with
    | nil       -> e1
    | (l, x, r) -> (l, x, r);

h ::  Tree a *  Tree a ->  Tree a;
h x y = x;

i :: a * a -> Bool;
i x y = x < y;

j :: Bool ->  Tree a;
j x =
  if x
    then nil
    else nil;

k :: a * a * a ->  Tree a;
k x y z =
  let p = x < y
  in
  if p
    then nil
    else
      let l = nil in
      let r = nil
      in
      (l, z, r);

(* test for (w :: var) rule *)
l1 :: a * a *  Tree a * a ->  Tree a;
l1 x y t a =
  let p = x < y
  in
  if p
    then nil
    else
      let n = nil
      in
      (t, a, n);

m :: Tree a -> a -> a -> Tree a
m t x y =
  let s = (t, y, t)
  in
  (t, x, s);

n1 :: (a -> Tree b) * a * b * Tree b -> Tree b
n1 f x y z =
  let l = f x in
  let r = (l, y, z)
  in
  (l, y, z);
