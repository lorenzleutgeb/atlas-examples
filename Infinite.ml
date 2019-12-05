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

infinite_10 ∷ Tree α → β
infinite_10 t = (let s = t in (infinite_10 t))

infinite_11 ∷ Tree α → β
infinite_11 t = (let s = t in (infinite_11 s))

infinite_12 ∷ α ⨯ Tree α → Tree α
infinite_12 x t = (let s = t in (infinite_12 x s, x, nil))

(**
 * The following is an interesting case, but the current implementation cannot type mutual recursion.
 *)
(*
infinite_na x t = (infinite_nb x t, x, nil)
infinite_nb x t = (infinite_na x t, x, nil)
*)
