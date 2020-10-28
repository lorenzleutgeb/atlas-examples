(**
 * The function definitions in this file are taken from or made to match
 * Section 6 of
 *
 *   Tobias Nipkow, Hauke Brinkop
 *   Amortized Complexity Verified
 *   Journal of Automated Reasoning, Vol. 62, Iss. 3, pp. 367-391
 *   https://doi.org/10.1007/s10817-018-9459-3
 *)

(**
 * Exposed definitions are
 *  - insert
 *  - delete
 *)

(**
 * The body of this definition is syntactically equal to `splay`, however
 * its annotation uses the real numbers and provides a lower bound.
 *)
splay_min ∷ Ord α ⇒ α ⨯ Tree α → Tree α | [[0 ↦ 1, (0 2) ↦ 1, (1 0) ↦ 5/2] → [0 ↦ 1, (0 2) ↦ 1], {[(1 0) ↦ 3/2] → [(1 0) ↦ 3/2], [] → [], [(1 0) ↦ 1/2] → [(1 0) ↦ 1/2]}]
splay_min a t = match t with
  | (cl, c, cr) → if a == c
    then (cl, c, cr)
    else if a < c
      then match cl with
        | leaf        → (leaf, c, cr)
        | (bl, b, br) → if a == b
          then (bl, a, (br, c, cr))
          else if a < b
            then match bl with
              | leaf → (leaf, b, (br, c, cr))
              | bl1  → match splay_min a bl1 with
                | leaf         → leaf
                | (al, a1, ar) → (al, a1, (ar, b, (br, c, cr)))
            else match br with
              | leaf → (bl, b, (leaf, c, cr))
              | br1  → match splay_min a br1 with
                | leaf         → leaf
                | (al, a1, ar) → ((bl, b, al), a1, (ar, c, cr))
      else match cr with
        | leaf        → (cl, c, leaf)
        | (bl, b, br) → if a == b
          then ((cl, c, bl), a, br)
          else if a < b
            then match bl with
              | leaf → ((cl, c, leaf), b, br)
              | bl1  → match splay_min a bl1 with
                | leaf         → leaf
                | (al, a1, ar) → ((cl, c, al), a1, (ar, b, br))
            else match br with
              | leaf → ((cl, c, bl), b, leaf)
              | br1  → match splay_min a br1 with
                | leaf         → leaf
                | (al, a1, ar) → (((cl, c, bl), b, al), a1, ar)

splay ∷ Ord α ⇒ α ⨯ Tree α → Tree α
splay a t = match t with
  | (cl, c, cr) → if a == c
    then (cl, c, cr)
    else if a < c
      then match cl with
        | leaf        → (leaf, c, cr)
        | (bl, b, br) → if a == b
          then (bl, a, (br, c, cr))
          else if a < b
            then match bl with
              | leaf → (leaf, b, (br, c, cr))
              | bl1  → match splay a bl1 with
                | leaf         → leaf
                | (al, a1, ar) → (al, a1, (ar, b, (br, c, cr)))
            else match br with
              | leaf → (bl, b, (leaf, c, cr))
              | br1  → match splay a br1 with
                | leaf         → leaf
                | (al, a1, ar) → ((bl, b, al), a1, (ar, c, cr))
      else match cr with
        | leaf        → (cl, c, leaf)
        | (bl, b, br) → if a == b
          then ((cl, c, bl), a, br)
          else if a < b
            then match bl with
              | leaf → ((cl, c, leaf), b, br)
              | bl1  → match splay a bl1 with
                | leaf         → leaf
                | (al, a1, ar) → ((cl, c, al), a1, (ar, b, br))
            else match br with
              | leaf → ((cl, c, bl), b, leaf)
              | br1  → match splay a br1 with
                | leaf         → leaf
                | (al, a1, ar) → (((cl, c, bl), b, al), a1, ar)

splay_max ∷ Tree α → Tree α
splay_max t = match t with
    | (l, b, r) → match r with
      | leaf        → (l, b, leaf)
      | (rl, c, rr) → match rr with
        | leaf →  ((l, b, rl), c, leaf)
        | rr1  → match splay_max rr1 with
          | leaf         → leaf
          | (rrl1, x, xa) → (((l, b, rl), c, rrl1), x, xa)

delete ∷ Ord α ⇒ α ⨯ Tree α → Tree α
delete a t = match t with
  | t1 → match splay a t1 with
    | leaf       → leaf
    | (l, a1, r) → if a == a1
      then match l with
        | leaf → r
        | l1   → match splay_max l1 with
          | leaf        → leaf
          | (ll1, m, _) → (ll1, m, r)
      else (l, a1, r)

insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert a t = match t with
  | leaf → (leaf, a, leaf)
  | t1   → match splay a t1 with
    | leaf       → leaf
    | (l, a1, r) → if a == a1
      then (l, a, r)
      else if a < a1
        then (l, a, (leaf, a1, r))
        else ((l, a1, leaf), a, r)

contains ∷ Ord α ⇒ α ⨯ Tree α → Bool
contains a t = match t with
  | leaf → false
  | t1   → match splay a t1 with
    | leaf       → false
    | (_, a1, _) → (a1 == a)