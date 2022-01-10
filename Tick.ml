f0 ∷ Tree α → Tree α
f0 t = let t1 ≔ ~ 1 2 t in t1

f1 ∷ Tree α → Tree α
f1 t = match t with
  | leaf        → leaf
  | (tl, x, tr) → ~ 1 2 (f1 tl)

f2 ∷ Tree α → Tree α
f2 t = match t with
  | leaf        → leaf
  | (tl, x, tr) → let t1 ≔ ~ 1 2 (f2 tl) in t1

(**
 * NOTE: Terminates only on `leaf`, but does not terminate on any other tree!
 *)
f3 ∷ Tree α → Tree α
f3 t = match t with
  | leaf → leaf
  | t    → let t1 ≔ ~ 1 2 (f3 t) in t1

(**
 * NOTE: Does not terminate.
 *)
f4 ∷ Tree α → Tree α
f4 t = let t1 ≔ ~ 1 2 (f4 t) in t1