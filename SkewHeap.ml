(**
 * The function definitions in this file are taken from or made to match
 * Section 5 of
 *
 *   Tobias Nipkow, Hauke Brinkop
 *   Amortized Complexity Verified
 *   Journal of Automated Reasoning, Vol. 62, Iss. 3, pp. 367-391
 *   https://doi.org/10.1007/s10817-018-9459-3
 *   https://dblp.org/rec/journals/jar/NipkowB19
 *
 * Nipkow and Brinkop use a potential function that counts the number
 * of "right heavy" nodes:
 *
 *   rh l r = if |l| < |r|
 *              then 1
 *              else 0
 *
 *   Φ leaf         = 0
 *   Φ (node l _ r) = Φ l + Φ r + rh l r
 *)

insert ∷ Ord α ⇒ (α ⨯ Tree α) → Tree α
insert x h = (merge (node leaf x leaf) h)

delete_min ∷ Ord α ⇒ (α ⨯ Tree α) → (Tree α ⨯ α)
delete_min z h = match h with
  | leaf       → (leaf, z)
  | node l x r → ((merge l r), x)

merge ∷ Ord α ⇒ (Tree α ⨯ Tree α) → Tree α
merge h1 h2 = match h1 with
  | leaf          → h2
  | node l1 a1 r1 → match h2 with
    | leaf             → (node l1 a1 r1)
    | node l2 a2 r2 → if a1 <= a2
      then (node (~ merge (node l2 a2 r2) r1) a1 l1)
      else (node (~ merge (node l1 x1 r1) r2) a2 l2)
