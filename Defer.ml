(**
 * Example for (tick:defer) by Florian Zuleger.
 *
 * Requires expert knowledge
 *
 *  ∀ t. rk(t) >= 1
 *
 * for weakening.
 *)
f ∷ Eq α ⇒ (α ⨯ Tree α) → Tree α | [[0 ↦ 1, (1 0) ↦ 1, (0 2) ↦ 1] → [0 ↦ 1, (0 2) ↦ 1], {}]
f x t = match t with
  | leaf       → leaf
  | node l y r → let fl = ~ f x l in let fr = ~ f x r in if x == y
    then fl
    else fr