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

splay ∷ Ord α ⇒ α ⨯ Tree α → Tree α | [[0 ↦ 1/2, (0 2) ↦ 1, (1 0) ↦ 3/2] → [0 ↦ 1/2, (0 2) ↦ 1], {[(1 0) ↦ 1] → [(1 0) ↦ 1], [(1 0) ↦ 1/2] → [(1 0) ↦ 1/2], [] → []}]
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
              | bl   → match ~ splay a bl with
                | (al, a1, ar) → (al, a1, (ar, b, (br, c, cr)))
            else match br with
              | leaf → (bl, b, (leaf, c, cr))
              | br   → match ~ splay a br with
                | (al, a1, ar) → ((bl, b, al), a1, (ar, c, cr))
      else match cr with
        | leaf        → (cl, c, leaf)
        | (bl, b, br) → if a == b
          then ((cl, c, bl), a, br)
          else if a < b
            then match bl with
              | leaf → ((cl, c, leaf), b, br)
              | bl   → match ~ splay a bl with
                | (al, a1, ar) → ((cl, c, al), a1, (ar, b, br))
            else match br with
              | leaf → ((cl, c, bl), b, leaf)
              | br   → match ~ splay a br with
                | (al, a1, ar) → (((cl, c, bl), b, al), a1, ar)

(**
 * The body of this definition is syntactically equal to `splay`, however
 * its annotation uses the integers.
 *)
splay_int ∷ Ord α ⇒ α ⨯ Tree α → Tree α | [[0 ↦ 1, (0 2) ↦ 1, (1 0) ↦ 3] → [0 ↦ 1, (0 2) ↦ 1], {[(1 0) ↦ 1] → [(1 0) ↦ 1], [(1 0) ↦ 2] → [(1 0) ↦ 2], [] → []}]
splay_int a t = match t with
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
              | bl   → match splay_int a bl with
                | (al, a1, ar) → (al, a1, (ar, b, (br, c, cr)))
            else match br with
              | leaf → (bl, b, (leaf, c, cr))
              | br   → match splay_int a br with
                | (al, a1, ar) → ((bl, b, al), a1, (ar, c, cr))
      else match cr with
        | leaf        → (cl, c, leaf)
        | (bl, b, br) → if a == b
          then ((cl, c, bl), a, br)
          else if a < b
            then match bl with
              | leaf → ((cl, c, leaf), b, br)
              | bl   → match splay_int a bl with
                | (al, a1, ar) → ((cl, c, al), a1, (ar, b, br))
            else match br with
              | leaf → ((cl, c, bl), b, leaf)
              | br   → match splay_int a br with
                | (al, a1, ar) → (((cl, c, bl), b, al), a1, ar)

(* splay_max_eq ∷ Eq (Tree α) ⇒ Tree α → Tree α | [[0 ↦ 1, (0 2) ↦ 1, (1 0) ↦ 3] → [0 ↦ 1, (0 2) ↦ 1], {[(1 0) ↦ 1] → [(1 0) ↦ 1], [(1 0) ↦ 2] → [(1 0) ↦ 2], [] → []}] *)
splay_max ∷ Tree α → Tree α
splay_max t = match t with
  | (l, b, r) → match r with
    | leaf        → (l, b, leaf)
    | (rl, c, rr) → match rr with
      | leaf →  ((l, b, rl), c, leaf)
      | rr   → match ~ splay_max rr with
        | (rrl1, x, xa) → (((l, b, rl), c, rrl1), x, xa)

delete ∷ Ord α ⇒ α ⨯ Tree α → Tree α
delete a t = match ~ splay a t with
  | (l, b, r) → if a == b
    then match l with
      | leaf → r
      | l    → match ~ splay_max l with
        | (ll1, m, _) → (ll1, m, r)
    else (l, b, r)

insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert a t = match t with
  | leaf → (leaf, a, leaf)
  | t    → match splay a t with
    | (l, b, r) → if a == b
      then (l, a, r)
      else if a < b
        then (l, a, (leaf, b, r))
        else ((l, b, leaf), a, r)

contains ∷ Ord α ⇒ α ⨯ Tree α → Bool
contains a t = match t with
  | leaf → false
  | t    → match splay a t with
    | leaf       → false
    | (_, b, _) → (a == b)

splay_zigzig ∷ α ⨯ Tree α → Tree α | [[0 ↦ 1/2, (0 2) ↦ 1, (1 0) ↦ 3/2] → [0 ↦ 1/2, (0 2) ↦ 1], {[(1 0) ↦ 1] → [(1 0) ↦ 1], [(1 0) ↦ 1/2] → [(1 0) ↦ 1/2], [] → []}]
splay_zigzig a t = match t with
  | (cl, c, cr) → match cl with
    | (bl, b, br) → match splay_zigzig a bl with
      | (al, a1, ar) → (al, a1, (ar, b, (br, c, cr)))
