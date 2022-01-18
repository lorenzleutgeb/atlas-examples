(**
 * The function definitions in this file are based on
 * Section 7 of
 *
 *   Tobias Nipkow, Hauke Brinkop
 *   Amortized Complexity Verified
 *   Journal of Automated Reasoning, Vol. 62, Iss. 3, pp. 367-391
 *   https://doi.org/10.1007/s10817-018-9459-3
 *)

(*

Version with literal numbers.

insert x h = match partition x h with
  | node l y r → (node l x r)

partition p t = match t with
  | leaf           → (node leaf 0 leaf)
  | node tab ab tbc → if ab <= p
    then match tbc with
      | leaf        → (node (node tab ab leaf) 0 leaf)
      | node tb b tc → if b <= p
        then match partition p tc with
          | node tc1 x tc2 → (node (node (node tab ab tb) b tc1) 0 tc2)
        else match partition p tb with
          | node tb1 x tb2 → (node (tab ab tb1) 0 (node tb2 b tc))
    else match tab with
      | leaf        → (node leaf 0 (node tab ab tbc))
      | node ta a tb → if a <= p
        then match partition p tb with
          | node tb1 x tb2 → (node (node ta a tb1) 0 (node tb2 ab tbc))
        else match partition p ta with
          | node ta1 x ta2 → (node ta1 0 (node ta2 a (node tb ab tbc)))
*)

insert ∷ Ord α ⇒ α ⨯ α ⨯ Tree α → Tree α | [[0 ↦ 1 / 2, (0 2) ↦ 5 / 2, (1 0) ↦ 3 / 4, (1 1) ↦ 1] → [0 ↦ 1 / 2, (0 2) ↦ 1], {}]
insert d x h = match ~ partition d x h with
  | leaf      → (node leaf x leaf)
  | node l _ r → (node l x r)

partition ∷ Ord α ⇒ α ⨯ α ⨯ Tree α → Tree α | [[0 ↦ 1 / 2, (0 2) ↦ 1, (1 0) ↦ 3 / 4, (1 1) ↦ 1] → [0 ↦ 1 / 2, (0 2) ↦ 1], {[(1 1) ↦ 1 / 2] → [(1 0) ↦ 1 / 2]}]
partition d p t = match t with
  | node tab ab tbc → if ab <= p
    then match tbc with
      | leaf        → (node (node tab ab leaf) d leaf)
      | node tb b tc → if b <= p
        then match ~ partition d p tc with
          | node tc1 _ tc2 → (node (node (node tab ab tb) b tc1) d tc2) (* zag zag *)
        else match ~ partition d p tb with
          | node tb1 _ tb2 → (node (node tab ab tb1) d (node tb2 b tc)) (* zag zig *)
    else match tab with
      | leaf        → (node leaf d (node leaf ab tbc))
      | node ta a tb → if a <= p
        then match ~ partition d p tb with
          | node tb1 _ tb2 → (node (node ta a tb1) d (node tb2 ab tbc)) (* zig zag *)
        else match ~ partition d p ta with
          | node ta1 _ ta2 → (node ta1 d (node ta2 a (node tb ab tbc))) (* zig zig *)

del_min ∷ Tree α → Tree α | [[0 ↦ 1 / 2, (0 2) ↦ 1, (1 0) ↦ 1] → [0 ↦ 1 / 2, (0 2) ↦ 1], {[(1 0) ↦ 1 / 4] → [(1 0) ↦ 1 / 4]}]
del_min t = match t with
  | node tab b tc → match tab with
    | leaf        → tc
    | node ta a tb → match ta with
      | leaf → (node tb b tc)
      | ta   → (node (~ del_min ta) a (node tb b tc))
