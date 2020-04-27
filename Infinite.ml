(** Contains function definitions that do not terminate. *)

infinite_1 ∷ α → Tree α
infinite_1 x = (infinite_1 x, x, infinite_1 x)

infinite_2 ∷ α ⨯ Tree α → Tree α
infinite_2 x t = (infinite_2 x t, x, t)

infinite_3 ∷ α ⨯ Tree α → Tree α
infinite_3 x t = (infinite_2 x t)

infinite_4 ∷ α ⨯ Tree α → Tree α
infinite_4 x t = (let s = t in infinite_3 x s)

infinite_5 ∷ α ⨯ Tree α → Tree α
infinite_5 x t = (let s = t in (infinite_5 x t, x, t))

infinite_6 ∷ α ⨯ Tree α ⨯ Tree α → Tree α
infinite_6 x t1 t2 = ((infinite_2 x t1), x, t2)

infinite_7 ∷ α ⨯ Tree α ⨯ Tree α → Tree α
infinite_7 x t1 t2 = (let s = t1 in ((infinite_2 x s), x, t2))

infinite_8 ∷ α ⨯ Tree α → Tree α
infinite_8 x t = (let s = t in (infinite_8 x s, x, s))

infinite_9 ∷ α ⨯ Tree α ⨯ Tree α → Tree α
infinite_9 x t1 t2 = (let s = t2 in (infinite_9 x s t1, x, t1))

(**
 * Requires sharing of t. Unused variable.
 * Tricky, since we do not know what β is. Probably we should
 * reject such inputs? How do we characterize them?
 *)
infinite_10 ∷ Tree α → β
infinite_10 t = (let s = t in (infinite_10 t))

(**
 * Same problem with β as in 10.
 *)
infinite_11 ∷ Tree α → β
infinite_11 t = (let s = t in (infinite_11 s))

(**
 * Similar to 11, but now we know the return type!
 * We will not have to apply (share) for x since it is not a
 * tree. The only complication is that the node constructor
 * will be let-normalized, generating two more let expresssions
 * (one binding `infinite_12 x s` the other binding `leaf`).
 *)
infinite_12 ∷ α ⨯ Tree α → Tree α
infinite_12 x t = (let s = t in (infinite_12 x s, x, leaf))

infinite_13 ∷ α ⨯ Tree α ⨯ Tree α → Tree α
infinite_13 x t u = (let s = t in (infinite_13 x s leaf, x, u))

infinite_14 ∷ α → Tree α
infinite_14 x = (infinite_14 x, x, leaf)

infinite_15 ∷ Tree α → Tree α
infinite_15 t = (let u = t in (infinite_15 u))

infinite_16 :: α -> β
infinite_16 t = (let u = t in infinite_16 u)

infinite_17 :: α -> β
infinite_17 x = (infinite_17 x)

infinite_18 :: Tree α -> Tree β
infinite_18 x = (infinite_18 x)

infinite_19a :: α ⨯ β → Tree α
infinite_19a x t = (infinite_19b x t, x, leaf)

infinite_19b :: α ⨯ β → Tree α
infinite_19b x t = (infinite_19a x t, x, leaf)
