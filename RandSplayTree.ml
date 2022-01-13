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

splay_max_only ∷ Tree α → Tree α
splay_max_only t = match t with
  | (l, b, r) → match r with
    | leaf        → (l, b, leaf)
    | (rl, c, rr) → match rr with
      | leaf → ((l, b, rl), c, leaf)
      | rr   → match ~ 1 2 splay_max_only rr with
        | (rrl1, x, xa) → if coin
            then ~ 1 2 (((l, b, rl), c, rrl1), x, xa) (* rotation *)
            else (l, b, (rl, c, (rrl1, x, xa))) (* no rotation *)

splay_max ∷ Tree α → Tree α
splay_max t = match t with
  | (l, b, r) → match r with
    | leaf        → (l, b, leaf)
    | (rl, c, rr) → match rr with
      | leaf → ((l, b, rl), c, leaf)
      | rr   → match ~ 1 2 splay_max rr with
        | (r1, max, ignored) → match r1 with
          | (rrl1, x, xa) → if coin
            then ~ 1 2 ((((l, b, rl), c, rrl1), x, xa), max, leaf) (* rotation *)
            else ((l, b, (rl, c, (rrl1, x, xa))), max, leaf) (* no rotation *)

delete ∷ Ord α ⇒ α ⨯ Tree α → Tree α
delete a t = match t with
  | (cl, c, cr) → if a == c
    then (splay_max_only cl, a (* Incorrect. *), cr)
    else if a < c
      then match cl with
        | leaf        → (leaf, c, cr)
        | (bl, b, br) → if a == b
          then ((splay_max_only bl, a (* Incorrect. *), br), c, cr)
          else if a < b
            then match bl with
              | leaf → (leaf, b, (br, c, cr))
              | bl   → match ~ 1 2 delete a bl with
                | (al, a1, ar) → if coin
                  then ~ 1 2 (al, a1, (ar, b, (br, c, cr)))
                  else (((al, a1, ar), b, br), c, cr)
            else match br with
              | leaf → (bl, b, (leaf, c, cr))
              | br   → match ~ 1 2 delete a br with
                | (al, a1, ar) → if coin
                  then ~ 1 2 ((bl, b, al), a1, (ar, c, cr))
                  else ((bl, b, (al, a1, ar)), c, cr)
      else match cr with
        | leaf → (cl, c, leaf)
        | (bl, b, br) → if a == b
          then (cl, c, (splay_max_only bl, a (* Incorrect. *), br))
          else if a < b
            then match bl with
              | leaf → ((cl, c, leaf), b, br)
              | bl   → match ~ 1 2 delete a bl with
                | (al, a1, ar) → if coin
                  then ~ 1 2 ((cl, c, al), a1, (ar, b, br))
                  else (cl, c, ((al, a1, ar), b, br))
            else match br with
              | leaf → ((cl, c, bl), b, leaf)
              | br   → match ~ 1 2 delete a br with
                | (al, a1, ar) → if coin
                  then ~ 1 2 (((cl, c, bl), b, al), a1, ar)
                  else (cl, c, (bl, b, (al, a1, ar)))

splay_all_zigzig ∷ Ord α ⇒ α ⨯ α ⨯ α ⨯ α ⨯ α ⨯ Tree α → Tree α
splay_all_zigzig mode modeContains modeDelete modeInsert a t = match t with
  | (cl, c, cr) → if a == c
    then if mode == modeContains
      then (* let result := true in *) (cl, c, cr)
      else if mode == modeDelete
        then match splay_max cl with
          | (cl1, max, ignored) → (cl1, max, cr)
        else (cl, c, cr)
    else match cl with
    | leaf        → if mode == modeInsert
      then ((leaf, a, leaf), c, cr)
      else (leaf, c, cr)
    | (bl, b, br) → match bl with
      | leaf → if mode == modeInsert
        then ((leaf, a, leaf), b, (br, c, cr))
        else (leaf, b, (br, c, cr))
      | bl   → match ~ 1 2 splay_all_zigzig mode modeContains modeDelete modeInsert a bl with
        | (al, a1, ar) → if coin
          then ~ 1 2 (al, a1, (ar, b, (br, c, cr)))
          else (((al, a1, ar), b, br), c, cr)