(**
 * The function definitions in this file are based on
 * Section 7 of
 *
 *   Tobias Nipkow, Hauke Brinkop
 *   Amortized Complexity Verified
 *   Journal of Automated Reasoning, Vol. 62, Iss. 3, pp. 367-391
 *   https://doi.org/10.1007/s10817-018-9459-3
 *   https://dblp.org/rec/journals/jar/NipkowB19
 *)

delete_min ∷ α ⨯ Tree α → (Tree α ⨯ α)
delete_min z t = match t with
  | leaf         → (leaf, z)
  | node tab b tc → match tab with
    | leaf        → (tc, b)
    | node ta a tb → match ta with
      | leaf → ((node tb b tc), a)
      | ta   → match ~ 1 2 delete_min z ta with
        | (t1, x) → if coin
          then ~ 1 2 ((node t1 a (node tb b tc)), x)
          else ((node (node t1 a tb) b tc), x)

insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert d t = match t with
  | node tab ab tbc → if ab <= d
    then match tbc with
      | leaf        → (node tab ab (node leaf d leaf))
      | node tb b tc → if b <= d
        then match ~ 1 2 insert d tc with (* zag zag *)
          | node tc1 c tc2 → if coin
            then ~ 1 2 (node (node (node tab ab tb) b tc1) c tc2)
            else (node tab ab (node tb b (node tc1 c tc2)))
        else match ~ 1 2 insert d tb with (* zag zig *)
          | node tb1 c tb2 → if coin
            then ~ 1 2 (node (node tab ab tb1) d (node tb2 b tc))
            else (node tab ab (node (node tb1 c tb2) b tc))
    else match tab with
      | leaf        → (node (node leaf d leaf) ab tbc)
      | node ta a tb → if a <= d
        then match ~ 1 2 insert d tb with (* zig zag *)
          | node tb1 c tb2 → if coin
            then ~ 1 2 (node (node ta a tb1) c (node tb2 ab tbc))
            else (node (node ta a (node tb1 c tb2)) ab tbc)
        else match ~ 1 2 insert d ta with (* zig zig *)
          | node ta1 c ta2 → if coin
            then ~ 1 2 (node ta1 c (node ta2 a (node tb ab tbc)))
            else (node (node (node ta1 c ta2) a tb) ab tbc)