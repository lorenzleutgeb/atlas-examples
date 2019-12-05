f ∷ Tree α ⨯ α ⨯ Tree α → Tree α
f l x r = (l, x, r);

g ∷ Tree α ⨯ Tree α → Tree α
g t e1 =
  match t with
    | leaf      → e1
    | (l, x, r) → (l, x, r);

h ∷  Tree α ⨯ Tree α → Tree α
h x y = x;

i ∷ Ord α ⇒ α ⨯ α → Bool
i x y = x < y;

j ∷ Bool → Tree α
j x =
  if x
    then leaf
    else leaf;

k ∷ Ord α ⇒ α ⨯ α ⨯ β → Tree β
k x y z =
  let p = x < y
  in
  if p
    then leaf
    else
      let l = leaf in
      let r = leaf
      in
      (l, z, r);

(* test for (w ∷ var) rule *)
l1 ∷ Ord α ⇒ α ⨯ α ⨯ Tree β ⨯ β → Tree β
l1 x y t a =
  let p = x < y
  in
  if p
    then leaf
    else
      let n = leaf
      in
      (t, a, n);

m ∷ Tree α ⨯ α ⨯ α → Tree α
m t x y =
  let s = (t, y, t)
  in
  (t, x, s);

