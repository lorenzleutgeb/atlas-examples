splay ∷ Ord α ⇒ α ⨯ Tree α → Tree α
splay a t = match t with
  | (cl, c, cr) → if a == c
    then (cl, c, cr)
    else if a < c
      then match cl with
        | leaf        → (leaf, c, cr)
        | (bl, b, br) → if a == b
          then ((bl, a, br), c, cr)  (* No rotation! *)
          else if a < b
            then match bl with
              | leaf → (leaf, b, (br, c, cr))
              | bl   → match ~ 1 2 splay a bl with
                | (al, a1, ar) → if coin
                  then ~ 1 2 (al, a1, (ar, b, (br, c, cr)))
                  else (((al, a1, ar), b, br), c, cr)
            else match br with
              | leaf → (bl, b, (leaf, c, cr))
              | br   → match ~ 1 2 splay a br with
                | (al, a1, ar) → if coin
                  then ~ 1 2 ((bl, b, al), a1, (ar, c, cr))
                  else ((bl, b, (al, a1, ar)), c, cr)
      else match cr with
        | leaf        → (cl, c, leaf)
        | (bl, b, br) → if a == b
          then (cl, c, (bl, a, br))  (* No rotation! *)
          else if a < b
            then match bl with
              | leaf → ((cl, c, leaf), b, br)
              | bl   → match ~ 1 2 splay a bl with
                | (al, a1, ar) → if coin
                  then ~ 1 2 ((cl, c, al), a1, (ar, b, br))
                  else (cl, c, ((al, a1, ar), b, br))
            else match br with
              | leaf → ((cl, c, bl), b, leaf)
              | br   → match ~ 1 2 splay a br with
                | (al, a1, ar) → if coin
                  then ~ 1 2 (((cl, c, bl), b, al), a1, ar)
                  else (cl, c, (bl, b, (al, a1, ar)))

insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert a t = match t with
  | (cl, c, cr) → if a == c
    then (cl, c, cr)
    else if a < c
      then match cl with
        | leaf        → ((leaf, a, leaf), c, cr)
        | (bl, b, br) → if a == b
          then ((bl, a, br), c, cr) (* Found. No rotation. *)
          else if a < b
            then match bl with
              | leaf → ((leaf, a, leaf), b, (br, c, cr))
              | bl   → match ~ 1 2 insert a bl with
                | (al, a1, ar) → if coin
                  then ~ 1 2 (al, a1, (ar, b, (br, c, cr)))
                  else (((al, a1, ar), b, br), c, cr)
            else match br with
              | leaf → (bl, b, ((leaf, a, leaf), c, cr))
              | br   → match ~ 1 2 insert a br with
                | (al, a1, ar) → if coin
                  then ~ 1 2 ((bl, b, al), a1, (ar, c, cr))
                  else ((bl, b, (al, a1, ar)), c, cr)
      else match cr with
        | leaf → (cl, c, (leaf, a, leaf))
        | (bl, b, br) → if a == b
          then (cl, c, (bl, a, br)) (* Found. No rotation. *)
          else if a < b
            then match bl with
              | leaf → ((cl, c, (leaf, a, leaf)), b, br)
              | bl   → match ~ 1 2 insert a bl with
                | (al, a1, ar) → if coin
                  then ~ 1 2 ((cl, c, al), a1, (ar, b, br))
                  else (cl, c, ((al, a1, ar), b, br))
            else match br with
              | leaf → ((cl, c, bl), b, (leaf, a, leaf))
              | br   → match ~ 1 2 insert a br with
                | (al, a1, ar) → if coin
                  then ~ 1 2 (((cl, c, bl), b, al), a1, ar)
                  else (cl, c, (bl, b, (al, a1, ar)))

splay_max ∷ α ⨯ Tree α → (Tree α ⨯ α)
splay_max z t = match t with
  | leaf      → {leaf, z}
  | (l, b, r) → match r with
    | leaf        → {(l, b, leaf), b}
    | (rl, c, rr) → match rr with
      | leaf → {((l, b, rl), c, leaf), c}
      | rr   → match ~ 1 2 splay_max z rr with
        | {r1, max} → match r1 with
          | leaf          → {leaf, z}
          | (rrl1, x, xa) → if coin
            then ~ 1 2 {(((l, b, rl), c, rrl1), x, xa), max} (* rotation *)
            else {(l, b, (rl, c, (rrl1, x, xa))), max} (* no rotation *)

delete ∷ Ord α ⇒ α ⨯ α ⨯ Tree α → Tree α
delete z a t = match t with
  | (cl, c, cr) → if a == c
    then match splay_max z cl with
      | {cl1, max} → (cl1, max, cr)
    else if a < c
      then match cl with
        | leaf        → (leaf, c, cr)
        | (bl, b, br) → if a == b
          then match splay_max z bl with
            | {bl1, max} → ((bl1, max, br), c, cr)
          else if a < b
            then match bl with
              | leaf → (leaf, b, (br, c, cr))
              | bl   → match ~ 1 2 delete z a bl with
                | (al, a1, ar) → if coin
                  then ~ 1 2 (al, a1, (ar, b, (br, c, cr)))
                  else (((al, a1, ar), b, br), c, cr)
            else match br with
              | leaf → (bl, b, (leaf, c, cr))
              | br   → match ~ 1 2 delete z a br with
                | (al, a1, ar) → if coin
                  then ~ 1 2 ((bl, b, al), a1, (ar, c, cr))
                  else ((bl, b, (al, a1, ar)), c, cr)
      else match cr with
        | leaf → (cl, c, leaf)
        | (bl, b, br) → if a == b
          then match splay_max z bl with
            | {bl1, max} → (cl, c, (bl1, max, br))
          else if a < b
            then match bl with
              | leaf → ((cl, c, leaf), b, br)
              | bl   → match ~ 1 2 delete z a bl with
                | (al, a1, ar) → if coin
                  then ~ 1 2 ((cl, c, al), a1, (ar, b, br))
                  else (cl, c, ((al, a1, ar), b, br))
            else match br with
              | leaf → ((cl, c, bl), b, leaf)
              | br   → match ~ 1 2 delete z a br with
                | (al, a1, ar) → if coin
                  then ~ 1 2 (((cl, c, bl), b, al), a1, ar)
                  else (cl, c, (bl, b, (al, a1, ar)))