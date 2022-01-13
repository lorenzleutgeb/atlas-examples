f0 ∷ Tree α → Tree α
f0 t = let t1 ≔ ~ 1 2 t in t1

f1 ∷ Tree α → Tree α
f1 t = match t with
  | (tl, x, tr) → ~ 1 2 (f1 tl)

f2 ∷ Tree α → Tree α
f2 t = match t with
  | (tl, x, tr) → let t1 ≔ ~ 1 2 (f2 tl) in t1

(**
 * NOTE: Terminates only on `leaf`, but does not terminate on any other tree!
 *)
f3 ∷ Tree α → Tree α
f3 t = match t with
  | t    → let t1 ≔ ~ 1 2 (f3 t) in t1

(**
 * NOTE: Does not terminate.
 *)
f4 ∷ Tree α → Tree α
f4 t = let t1 ≔ ~ 1 2 (f4 t) in t1

f5 ∷ Tree α * α → Tree α
f5 t a = match t with
  | leaf        → (leaf, a, leaf)
  | (tl, x, tr) → ~ 1 2 (f5 tl a)

f6 ∷ Tree α * α → Tree α
f6 t a = match t with
  | leaf        → (leaf, a, leaf)
  | (tl, x, tr) → ~ 1 2 let t1 ≔ f6 tl a in t1

f7 ∷ Tree α * α → Tree α
f7 t a = match t with
  | leaf        → (leaf, a, leaf)
  | (tl, x, tr) → let t1 ≔ ~ 1 2 (f7 tl a) in t1

h ∷ Tree α → Tree α
h t = let t1 ≔ ~ 1 2 (h t) in t1

id ∷ Tree α → Tree α
id t = t

id2 ∷ Tree α → Tree α
id2 t = id t

id3 ∷ Tree α → Tree α
id3 t = ~ id t

id4 ∷ Tree α → Tree α
id4 t = let d ≔ ~ id t in d

test ∷ Tree α ⨯ Tree α ⨯ Tree α ⨯ α → Tree α
test a b c dummy = let c1 = id c in (((c1, dummy, b), dummy, a), dummy, leaf)

test5 ∷ Tree α ⨯ Tree α ⨯ Tree α ⨯ α → Tree α
test5 a b c dummy = let c' = id c in ((c',dummy,b),dummy,a)

test6 ∷ Tree α ⨯ Tree α ⨯ α → Tree α
test6 b c dummy = let c' = id c in (c',dummy,b)

test7 ∷ Tree α ⨯ Tree α ⨯ Tree α ⨯ α → Tree α
test7 a b c dummy = let c' = id c in (c',dummy,b)

test2 ∷ Tree α ⨯ Tree α ⨯ α → Tree α
test2 b c dummy = let c1 = id c in ((c1, dummy, b), dummy, leaf)

test3 ∷ Tree α ⨯ α → Tree α
test3 c dummy = let c1 = id c in (c1, dummy, leaf)

test4 ∷ Tree α ⨯ α → Tree α
test4 c dummy = (c, dummy, leaf)
