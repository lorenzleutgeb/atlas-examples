(**
 * The function definitions in this file are taken from or made to match
 * Section 5 of
 *
 *   Tobias Nipkow, Hauke Brinkop
 *   Amortized Complexity Verified
 *   Journal of Automated Reasoning, Vol. 62, Iss. 3, pp. 367-391
 *   https://doi.org/10.1007/s10817-018-9459-3
 *)

del_min ∷ Ord α ⇒ α ⨯ Tree α → (Tree α ⨯ α)
del_min z h = match h with
  | leaf      → (leaf, z)
  | node l x r → ((merge l r), x)

insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert x h = (merge (node leaf a leaf) h)

merge ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α
merge h1 h2 = match h1 with
  | leaf            → h2
  | node h1l h1x h1r → match h2 with
    | leaf            → (node h1l h1x h1r)
    | node h2l h2x h2r → if h1x < h2x
      then (node (~ merge (node (node h2l h2x h2r) h1r)) h1x h1l)
      else (node (~ merge (node (node h1l h1x h1r) h2r)) h2x h2l)