(**
 * The function definitions in this file are taken from or made to match
 * Section 6 of
 *
 *   Tobias Nipkow, Hauke Brinkop
 *   Amortized Complexity Verified
 *   Journal of Automated Reasoning, Vol. 62, Iss. 3, pp. 367-391
 *   https://doi.org/10.1007/s10817-018-9459-3
 *)

splay_eq ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Tree α
splay_eq a t = match t with
  | leaf        → leaf
  | (cl, c, cr) → if a == c
    then (cl, c, cr)
    else if a < c
      then match cl with
        | leaf        → (leaf, c, cr)
        | (bl, b, br) → if a == b
          then (bl, a, (br, c, cr))
          else if a < b
            then if bl == leaf
              then (bl, b, (br, c, cr))
              else match splay_eq a bl with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → (al, a', (ar, b, (br, c, cr))) (* zig zig *)
            else if br == leaf
              then (bl, b, (br, c, cr))
              else match splay_eq a br with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → ((bl, b, al), a', (ar, c, cr)) (* zig zag *)
      else match cr with
        | leaf        → (cl, c, leaf)
        | (bl, b, br) → if a == b
          then ((cl, c, bl), a, br)
          else if a < b
            then if bl == leaf
              then ((cl, c, bl), b, br)
              else match splay_eq a bl with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → ((cl, c, al), a', (ar, b, br)) (* zag zig *)
            else if br == leaf
              then ((cl, c, bl), b, br)
              else match splay_eq a br with
                | leaf         → leaf (* TODO: undefined *)
                | (al, x, xa) → (((cl, c, bl), b, al), x, xa) (* zag zag *)

(* A variant of splay_eq where the zig-zig case uses Georg Moser's LNF variant.
 *)
splay_eq_glnf ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Tree α
splay_eq_glnf a t = match t with
  | leaf        → leaf
  | (cl, c, cr) → if a == c
    then (cl, c, cr)
    else if a < c
      then match cl with
        | leaf        → (leaf, c, cr)
        | (bl, b, br) → if a == b
          then (bl, a, (br, c, cr))
          else if a < b
            then if bl == leaf
              then (leaf, b, (br, c, cr))
              else match splay_eq_glnf a bl with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → (let t'' = (let t''' = (br, c, cr) in (ar, b, t''')) in (al, a, t''))
            else if br == leaf
              then (bl, b, (leaf, c, cr))
              else match splay_eq_glnf a br with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → ((bl, b, al), a', (ar, c, cr))
      else match cr with
        | leaf        → (cl, c, leaf)
        | (bl, b, br) → if a == b
          then ((cl, c, bl), a, br)
          else if a < b
            then if bl == leaf
              then ((cl, c, leaf), b, br)
              else match splay_eq_glnf a bl with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → ((cl, c, al), a', (ar, b, br))
            else if br == leaf
              then ((cl, c, bl), b, leaf)
              else match splay_eq_glnf a br with
                | leaf        → leaf (* TODO: undefined *)
                | (al, x, xa) → (((cl, c, bl), b, al), x, xa)

splay ∷ Ord α ⇒ α ⨯ Tree α → Tree α
splay a t = match t with
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
              | (bll, blx, blr) → match splay a (bll, blx, blr) with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → (al, a', (ar, b, (br, c, cr)))
            else match br with
              | leaf            → (bl, b, (leaf, c, cr))
              | (brl, brx, brr) → match splay a (brl, brx, brr) with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → ((bl, b, al), a', (ar, c, cr))
      else match cr with
        | leaf        → (cl, c, leaf)
        | (bl, b, br) → if a == b
          then ((cl, c, bl), a, br)
          else if a < b
            then match bl with
              | leaf            → ((cl, c, leaf), b, br)
              | (bll, blx, blr) → match splay a (bll, blx, blr) with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → ((cl, c, al), a', (ar, b, br))
            else match br with
              | leaf            → ((cl, c, bl), b, leaf)
              | (brl, brx, brr) → match splay a (brl, brx, brr) with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → (((cl, c, bl), b, al), a', ar)

(* We make the assumption that a < b < c and use this to simplify splay.
 * Since we do not need to compare elements anymore, we can drop the constraint
 * Ord α.
 *)
splay_eq_zigzig ∷ Eq (Tree α) ⇒ α ⨯ Tree α → Tree α
splay_eq_zigzig a t = match t with
    | leaf        → leaf
    | (cl, c, cr) → match cl with (* NOTE: We assume that a != c *)
        | leaf        → (leaf, c, cr)
        | (bl, b, br) → if bl == leaf (* NOTE: We assume that a != b *)
            then (bl, b, (br, c, cr))
            else match splay_eq_zigzig a bl with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → (al, a', (ar, b, (br, c, cr)))

(* We make the assumption that a < b < c and use this to simplify splay.
 * Since we do not need to compare elements anymore, we can drop the constraint
 * Ord α.
 *
 * TODO: Should we also assume t != leaf and bl != leaf?
 *)
splay_zigzig ∷ α ⨯ Tree α → Tree α
splay_zigzig a t = match t with
    | leaf        → leaf
    | (cl, c, cr) → match cl with (* NOTE: We assume that a != c *)
        | leaf        → (leaf, c, cr)
        | (bl, b, br) → match bl with (* NOTE: We assume that a != b *)
            | leaf            → (leaf, b, (br, c, cr))
            | (bll, blx, blr) → match splay_zigzig a (bll, blx, blr) with
                | leaf         → leaf (* TODO: undefined *)
                | (al, a', ar) → (al, a', (ar, b, (br, c, cr)))

splay_max_eq ∷ Eq (Tree α) ⇒ Tree α → Tree α
splay_max_eq t = match t with
    | leaf      → leaf
    | (l, b, r) → match r with
        | leaf        → (l, b, leaf)
        | (rl, c, rr) → if rr == leaf
            then ((l, b, rl), c, leaf)
            else match splay_max_eq rr with
                | leaf          → leaf (* TODO: undefined *)
                | (rrl, x, xa)  → (((l, b, rl), c, rrl), x, xa)

splay_max ∷ Tree α → Tree α
splay_max t = match t with
    | leaf      → leaf
    | (l, b, r) → match r with
        | leaf        → (l, b, leaf)
        | (rl, c, rr) → match rr with
            | leaf            →  ((l, b, rl), c, leaf)
            | (rrl, rrx, rrr) → match splay_max (rrl, rrx, rrr) with
                | leaf          → leaf (* TODO: undefined *)
                | (rrl', x, xa) → (((l, b, rl), c, rrl'), x, xa)

delete_eq ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Tree α
delete_eq a t = if t == leaf
  then leaf
  else match splay_eq a t with
    | leaf       → leaf (* TODO: undefined *)
    | (l, a', r) → if a == a'
      then if l == leaf
        then r
        else match splay_max_eq l with
          | leaf        → leaf (* TODO: undefined *)
          | (l', m, r') → (l', m, r)
      else (l, a', r)

delete ∷ Ord α ⇒ α ⨯ Tree α → Tree α
delete a t = match t with
  | leaf         → leaf
  | (tl, tx, tr) → match splay a (tl, tx, tr) with
    | leaf       → leaf (* TODO: undefined *)
    | (l, a', r) → if a == a'
      then match l with
        | leaf         → r
        | (ll, lx, lr) → match splay_max (ll, lx, lr) with
          | leaf          → leaf (* TODO: undefined *)
          | (ll', m, lr') → (ll', m, r)
      else (l, a', r)

insert_eq ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Tree α
insert_eq a t = if t == leaf
  then (leaf, a, leaf)
  else match splay_eq a t with
    | leaf       → leaf (* TODO: undefined *)
    | (l, a', r) → if a == a'
      then (l, a, r)
      else if a < a'
        then (l, a, (leaf, a', r))
        else ((l, a', leaf), a, r)

insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert a t = match t with
  | leaf         → (leaf, a, leaf)
  | (tl, tx, tr) → match splay a (tl, tx, tr) with
    | leaf       → leaf (* TODO: undefined *)
    | (l, a', r) → if a == a'
      then (l, a, r)
      else if a < a'
        then (l, a, (leaf, a', r))
        else ((l, a', leaf), a, r)

contains_eq ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Bool
contains_eq a t = match t with
  | leaf      → false
  | (l, x, r) → match splay_eq a (l, x, r) with
    | leaf         → false
    | (l2, x2, r2) → (x2 == a)

contains ∷ Ord α ⇒ α ⨯ Tree α → Bool
contains a t = match t with
  | leaf      → false
  | (l, x, r) → match splay a (l, x, r) with
    | leaf         → false
    | (l2, x2, r2) → (x2 == a)