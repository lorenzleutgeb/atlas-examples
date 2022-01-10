f ∷ Tree α → Tree α
f t = let t1 ≔ ~ 1 2 t in t1

(**
 * NOTE: Terminates only on leaf, but does not terminate on any other Tree
 *)
g ∷ Tree α → Tree α
g t = match t with
  | leaf → leaf
  | t    → let t1 ≔ ~ 1 2 (g t) in t1

(**
 * NOTE: Terminates.
 *)
gl ∷ Tree α → Tree α
gl t = match t with
  | leaf        → leaf
  | (tl, x, tr) → let t1 ≔ ~ 1 2 (gl tl) in t1

h ∷ Tree α → Tree α
h t = let t1 ≔ ~ 1 2 (h t) in t1