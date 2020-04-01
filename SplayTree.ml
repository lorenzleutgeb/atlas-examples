splay ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Tree α
splay a t = match t with
  | leaf        → leaf
  | (cl, c, cr) → if a == c
    then (cl, c, cr)
    else if a < c
      then match cl with
        | leaf         → (leaf, c, cr)
        | (bl, b, br) → if a == b
          then (bl, a, (br, c, cr))
          else if a < b
            then if bl == leaf
              then (bl, b, (br, c, cr))
              else match splay a bl with
                | leaf          → leaf (* TODO: undefined *)
                | (al, a', ar) → (al, a', (ar, b, (br, c, cr)))
            else if br == leaf
              then (bl, b, (br, c, cr))
              else match splay a br with
                | leaf          → leaf (* TODO: undefined *)
                | (al, a', ar) → ((bl, b, al), a', (ar, c, cr))
      else match cr with
        | leaf         → (cl, c, leaf)
        | (bl, b, br) → if a == b
          then ((cl, c, bl), a, br)
          else if a < b
            then if bl == leaf
              then ((cl, c, bl), b, br)
              else match splay a bl with
                | leaf          → leaf (* TODO: undefined *)
                | (al, a', ar) → ((cl, c, al), a', (ar, b, br))
            else if br == leaf
              then ((cl, c, bl), b, br)
              else match splay a br with
                | leaf         → leaf (* TODO: undefined *)
                | (al, x, xa) → (((cl, c, bl), b, al), x, xa)

splay_noeq ∷ Ord α ⇒ α ⨯ Tree α → Tree α
splay_noeq a t = match t with
  | leaf        → leaf
  | (cl, c, cr) → if a == c
    then (cl, c, cr)
    else if a < c
      then match cl with
        | leaf        → (leaf, c, cr)
        | (bl, b, br) → if a == b
          then (bl, a, (br, c, cr))
          else if a < b
            then match bl with
              | leaf            → (leaf, b, (br, c, cr))
              | (bll, blx, blr) → match splay_noeq a (bll, blx, blr) with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → (al, a', (ar, b, (br, c, cr)))
            else match br with
              | leaf            → (bl, b, (leaf, c, cr))
              | (brl, brx, brr) → match splay_noeq a (brl, brx, brr) with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → ((bl, b, al), a', (ar, c, cr))
      else match cr with
        | leaf        → (cl, c, leaf)
        | (bl, b, br) → if a == b
          then ((cl, c, bl), a, br)
          else if a < b
            then match bl with
              | leaf            → ((cl, c, leaf), b, br)
              | (bll, blx, blr) → match splay_noeq a (bll, blx, blr) with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → ((cl, c, al), a', (ar, b, br))
            else match br with
              | leaf            → ((cl, c, bl), b, leaf)
              | (brl, brx, brr) → match splay_noeq a (brl, brx, brr) with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → (((cl, c, bl), b, al), a', ar)

(* We make the assumption that a < b < c and use this to simplify splay.
 * Since we do not need to compare elements anymore, we can drop the constraint
 * Ord α.
 *)
splay_zigzig ∷ Eq (Tree α) ⇒ α ⨯ Tree α → Tree α
splay_zigzig a t = match t with
    | leaf        → leaf
    | (cl, c, cr) → match cl with (* NOTE: We assume that a != c *)
        | leaf        → (leaf, c, cr)
        | (bl, b, br) → if bl == leaf (* NOTE: We assume that a != b *)
            then (bl, b, (br, c, cr))
            else match splay_zigzig a bl with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → (al, a', (ar, b, (br, c, cr)))

(* We make the assumption that a < b < c and use this to simplify splay_noeq.
 * Since we do not need to compare elements anymore, we can drop the constraint
 * Ord α.
 *)
splay_noeq_zigzig ∷ α ⨯ Tree α → Tree α
splay_noeq_zigzig a t = match t with
    | leaf        → leaf
    | (cl, c, cr) → match cl with (* NOTE: We assume that a != c *)
        | leaf        → (leaf, c, cr)
        | (bl, b, br) → match bl with (* NOTE: We assume that a != b *)
            | leaf            → (leaf, b, (br, c, cr))
            | (bll, blx, blr) → match splay_noeq_zigzig a (bll, blx, blr) with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → (al, a', (ar, b, (br, c, cr)))

splay_max ∷ Eq (Tree α) ⇒ Tree α → Tree α
splay_max t = match t with
    | leaf      → leaf
    | (l, b, r) → match r with
        | leaf         → (l, b, leaf)
        | (rl, c, rr) → if rr == leaf
            then ((l, b, rl), c, leaf)
            else match splay_max rr with
                | leaf          → leaf (* TODO: undefined *)
                | (rrl, x, xa)  → (((l, b, rl), c, rrl), x, xa)

splay_max_noeq ∷ Tree α → Tree α
splay_max_noeq t = match t with
    | leaf      → leaf
    | (l, b, r) → match r with
        | leaf         → (l, b, leaf)
        | (rl, c, rr) → match rr with
            | leaf            →  ((l, b, rl), c, leaf)
            | (rrl, rrx, rrr) → match splay_max_noeq (rrl, rrx, rrr) with
                | leaf          → leaf (* TODO: undefined *)
                | (rrl', x, xa) → (((l, b, rl), c, rrl'), x, xa)

delete ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Tree α
delete a t = if t == leaf
  then leaf
  else match splay a t with
    | leaf       → leaf (* TODO: undefined *)
    | (l, a', r) → if a == a'
      then if l == leaf
        then r
        else match splay_max l with
          | leaf        → leaf (* TODO: undefined *)
          | (l', m, r') → (l', m, r)
      else (l, a', r)

delete_noeq ∷ Ord α ⇒ α ⨯ Tree α → Tree α
delete_noeq a t = match t with
  | leaf         → leaf
  | (tl, tx, tr) → match splay_noeq a (tl, tx, tr) with
    | leaf       → leaf (* TODO: undefined *)
    | (l, a', r) → if a == a'
      then match l with
        | leaf         → r
        | (ll, lx, lr) → match splay_max_noeq (ll, lx, lr) with
          | leaf          → leaf (* TODO: undefined *)
          | (ll', m, lr') → (ll', m, r)
      else (l, a', r)

insert ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Tree α
insert a t = if t == leaf
  then (leaf, a, leaf)
  else match splay a t with
    | leaf       → leaf (* TODO: undefined *)
    | (l, a', r) → if a == a'
      then (l, a, r)
      else if a < a'
        then (l, a, (leaf, a', r))
        else ((l, a', leaf), a, r)

contains ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Bool
contains a t = match t with
  | leaf      → false
  | (l, x, r) → match splay a (l, x, r) with
    | leaf         → false
    | (l2, x2, r2) → (x2 == a)

contains_noeq ∷ Ord α ⇒ α ⨯ Tree α → Bool
contains_noeq a t = match t with
  | leaf      → false
  | (l, x, r) → match splay_noeq a (l, x, r) with
    | leaf         → false
    | (l2, x2, r2) → (x2 == a)
