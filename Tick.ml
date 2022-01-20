f0 ∷ Tree α → Tree α
f0 t = let t1 ≔ ~ 1/2 t in t1

f1 ∷ Tree α → Tree α
f1 t = match t with
  | node tl x tr → ~ 1/2 (f1 tl)

f2 ∷ Tree α → Tree α
f2 t = match t with
  | node tl x tr → let t1 ≔ ~ 1/2 (f2 tl) in t1

(**
 * NOTE: Terminates only on `leaf`, but does not terminate on any other tree!
 *)
f3 ∷ Tree α → Tree α
f3 t = match t with
  | t    → let t1 ≔ ~ 1/2 (f3 t) in t1

(**
 * NOTE: Does not terminate.
 *)
f4 ∷ Tree α → Tree α
f4 t = let t1 ≔ ~ 1/2 (f4 t) in t1

f5 ∷ (Tree α ⨯ α) → Tree α
f5 t a = match t with
  | leaf        → (node leaf a leaf)
  | node tl x tr → ~ 1/2 (f5 tl a)

f6 ∷ (Tree α ⨯ α) → Tree α
f6 t a = match t with
  | leaf        → (node leaf a leaf)
  | node tl x tr → ~ 1/2 let t1 ≔ f6 tl a in t1

f7 ∷ (Tree α ⨯ α) → Tree α
f7 t a = match t with
  | leaf        → (node leaf a leaf)
  | node tl x tr → let t1 ≔ ~ 1/2 (f7 tl a) in t1