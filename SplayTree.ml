(**
 * The function definitions in this file are taken from or made to match
 * Section 6 of
 *
 *   Tobias Nipkow, Hauke Brinkop
 *   Amortized Complexity Verified
 *   Journal of Automated Reasoning, Vol. 62, Iss. 3, pp. 367-391
 *   https://doi.org/10.1007/s10817-018-9459-3
 *   https://dblp.org/rec/journals/jar/NipkowB19
 *)

splay ∷ Ord α ⇒ (α ⨯ Tree α) → Tree α | [[0 ↦ 1/2, (0 2) ↦ 1, (1 0) ↦ 3/2] → [0 ↦ 1/2, (0 2) ↦ 1], {[(1 0) ↦ 1/2] → [(1 0) ↦ 1/2]}]
splay a t = match t with
  | node cl c cr → if a == c
    then node cl c cr
    else if a < c
      then match cl with
        | leaf         → node leaf c cr
        | node bl b br → if a == b
          then node bl a (node br c cr)
          else if a < b
            then match bl with
              | leaf → node leaf b (node br c cr)
              | bl   → match ~ splay a bl with
                | node al _ ar → node al a (node ar b (node br c cr))
            else match br with
              | leaf → node bl b (node leaf c cr)
              | br   → match ~ splay a br with
                | node al _ ar → node (node bl b al) a (node ar c cr)
      else match cr with
        | leaf        → node cl c leaf
        | node bl b br → if a == b
          then node (node cl c bl) a br
          else if a < b
            then match bl with
              | leaf → node (node cl c leaf) b br
              | bl   → match ~ splay a bl with
                | node al _ ar → node (node cl c al) a (node ar b br)
            else match br with
              | leaf → node (node cl c bl) b leaf
              | br   → match ~ splay a br with
                | node al _ ar → node (node (node cl c bl) b al) a ar

splay_max ∷ Tree α → Tree α | [[0 ↦ 1/2, (0 2) ↦ 1, (1 0) ↦ 3/2] → [0 ↦ 1/2, (0 2) ↦ 1], {[(1 0) ↦ 1/2] → [(1 0) ↦ 1/2]}]
splay_max t = match t with
  | node l b r → match r with
    | leaf         → node l b leaf
    | node rl c rr → match rr with
      | leaf → node (node l b rl) c leaf
      | rr   → match ~ splay_max rr with
        | node rrl1 x xa → node (node (node l b rl) c rrl1) x xa

delete ∷ Ord α ⇒ (α ⨯ Tree α) → Tree α | [[0 ↦ 1/2, (0 2) ↦ 3, (1 0) ↦ 5/2] → [0 ↦ 1/2, (0 2) ↦ 1], {}]
delete a t = match ~ splay a t with
  | node l b r → if a == b
    then match l with
      | leaf → r
      | l    → match ~ splay_max l with
        | node ll m _ → node ll m r
    else node l b r

insert ∷ Ord α ⇒ (α ⨯ Tree α) → Tree α | [[0 ↦ 1/2, (0 2) ↦ 3/2, (1 0) ↦ 2] → [0 ↦ 1/2, (0 2) ↦ 1], {}]
insert a t = match t with
  | leaf → node leaf a leaf
  | t    → match splay a t with
    | node l b r → if a == b
      then node l a r
      else if a < b
        then node l a (node leaf b r)
        else node (node l b leaf) a r

contains ∷ Ord α ⇒ (α ⨯ Tree α) → Bool
contains a t = match t with
  | leaf → false
  | t    → match splay a t with
    | leaf       → false
    | node _ b _ → (a == b)
