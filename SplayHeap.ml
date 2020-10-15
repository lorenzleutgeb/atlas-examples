(*

Version with literal numbers.

insert x h = match partition x h with
  | leaf      → leaf
  | (l, y, r) → (l, x, r)

partition p t = match t with
  | leaf           → (leaf, 0, leaf)
  | (tab, ab, tbc) → if ab <= p
    then match tbc with
      | leaf        → ((tab, ab, tbc), 0, leaf)
      | (tb, b, tc) → if b <= p
        then match partition p tc with
          | leaf          → leaf
          | (tc1, x, tc2) → (((tab, ab, tb), b, tc1), 0, tc2)
        else match partition p tb with
          | leaf          → leaf
          | (tb1, x, tb2) → ((tab ab tb1), 0, (tb2, b, tc))
    else match tab with
      | leaf        → (leaf, 0, (tab, ab, tbc))
      | (ta, a, tb) → if a <= p
        then match partition p tb with
          | leaf          → leaf
          | (tb1, x, tb2) → ((ta, a, tb1), 0, (tb2, ab, tbc))
        else match partition p ta with
          | leaf          → leaf
          | (ta1, x, ta2) → (ta1, 0, (ta2, a, (tb, ab, tbc)))
*)

insert ∷ Ord α ⇒ α ⨯ α ⨯ Tree α → Tree α
insert d x h = match partition d x h with
  | leaf      → leaf
  | (l, y, r) → (l, x, r)

partition ∷ Ord α ⇒ α ⨯ α ⨯ Tree α → Tree α
partition d p t = match t with
  | leaf           → (leaf, d, leaf)
  | (tab, ab, tbc) → if ab <= p
    then match tbc with
      | leaf → ((tab, ab, leaf), d, leaf)
      | (tb, b, tc) → if b <= p
        then match partition d p tc with
          | leaf          → leaf
          | (tc1, x, tc2) → (((tab, ab, tb), b, tc1), d, tc2)
        else match partition d p tb with
          | leaf          → leaf
          | (tb1, x, tb2) → ((tab, ab, tb1), d, (tb2, b, tc))
    else match tab with
      | leaf → (leaf, d, (leaf, ab, tbc))
      | (ta, a, tb) → if a <= p
        then match partition d p tb with
          | leaf          → leaf
          | (tb1, x, tb2) → ((ta, a, tb1), d, (tb2, ab, tbc))
        else match partition d p ta with
          | leaf          → leaf
          | (ta1, x, ta2) → (ta1, d, (ta2, a, (tb, ab, tbc)))