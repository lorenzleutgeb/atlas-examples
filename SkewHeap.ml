(**
 * The function definitions in this file are taken from or made to match
 * Section 5 of
 *
 *   Tobias Nipkow, Hauke Brinkop
 *   Amortized Complexity Verified
 *   Journal of Automated Reasoning, Vol. 62, Iss. 3, pp. 367-391
 *   https://doi.org/10.1007/s10817-018-9459-3
 *)

del_min ∷ Ord α ⇒ Tree α → Tree α
del_min t = match t with
  | leaf      → leaf
  | (l, m, r) → (merge l r)

insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert a h = (merge (leaf, a, leaf) h)
(* insert a h = (merge (Tree.singleton a) h) *)

merge ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α
merge h1 h2 = match h1 with
  | leaf         → h2
  | (l1, a1, r1) → match h2 with
    | leaf         → (l1, a1, r1)
    | (l2, a2, r2) → if a1 < a2
      then ((merge (l2, a2, r2) r1), a1, l1)
      else ((merge (l1, a1, r1) r2), a2, l2)
