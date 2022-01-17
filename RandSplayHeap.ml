(**
 * The function definitions in this file are based on
 * Section 7 of
 *
 *   Tobias Nipkow, Hauke Brinkop
 *   Amortized Complexity Verified
 *   Journal of Automated Reasoning, Vol. 62, Iss. 3, pp. 367-391
 *   https://doi.org/10.1007/s10817-018-9459-3
 *)

del_min ∷ α ⨯ Tree α → (Tree α ⨯ α)
del_min z t = match t with
  | leaf         → {leaf, z}
  | (tab, b, tc) → match tab with
    | leaf        → {tc, b}
    | (ta, a, tb) → match ta with
      | leaf → {(tb, b, tc), a}
      | ta   → match ~ 1 2 del_min z ta with
        | {t1, x} → if coin
          then ~ 1 2 {(t1, a, (tb, b, tc)), x}
          else {((t1, a, tb), b, tc), x}

insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert d t = match t with
  | (tab, ab, tbc) → if ab <= d
    then match tbc with
      | leaf        → (tab, ab, (leaf, d, leaf))
      | (tb, b, tc) → if b <= d
        then match ~ 1 2 insert d tc with (* zag zag *)
          | (tc1, c, tc2) → if coin
            then ~ 1 2 (((tab, ab, tb), b, tc1), c, tc2)
            else (tab, ab, (tb, b, (tc1, c, tc2)))
        else match ~ 1 2 insert d tb with (* zag zig *)
          | (tb1, c, tb2) → if coin
            then ~ 1 2 ((tab, ab, tb1), d, (tb2, b, tc))
            else (tab, ab, ((tb1, c, tb2), b, tc))
    else match tab with
      | leaf        → ((leaf, d, leaf), ab, tbc)
      | (ta, a, tb) → if a <= d
        then match ~ 1 2 insert d tb with (* zig zag *)
          | (tb1, c, tb2) → if coin
            then ~ 1 2 ((ta, a, tb1), c, (tb2, ab, tbc))
            else ((ta, a, (tb1, c, tb2)), ab, tbc)
        else match ~ 1 2 insert d ta with (* zig zig *)
          | (ta1, c, ta2) → if coin
            then ~ 1 2 (ta1, c, (ta2, a, (tb, ab, tbc)))
            else (((ta1, c, ta2), a, tb), ab, tbc)