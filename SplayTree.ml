(* TODO: Version that does not need Eq (Tree α)? *)
splay ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Tree α
splay a t = match t with
    | leaf         → leaf
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
                                | leaf          → leaf
                                | (al, a', ar) → (al, a', (ar, b, (br, c, cr)))
                    else if br == leaf
                        then (bl, b, (br, c, cr))
                        else match splay a br with
                            | leaf          → leaf
                            | (al, a', ar) → ((bl, b, al), a', (ar, c, cr))
            else match cr with
                | leaf         → (cl, c, leaf)
                | (bl, b, br) → if a == b
                    then ((cl, c, bl), a, br)
                    else if a < b
                        then if bl == leaf
                            then ((cl, c, bl), b, br)
                            else match splay a bl with
                                | leaf          → leaf
                                | (al, a', ar) → ((cl, c, al), a', (ar, b, br))
                        else if br == leaf
                            then ((cl, c, bl), b, br)
                            else match splay a br with
                                | leaf         → leaf
                                | (al, x, xa) → (((cl, c, bl), b, al), x, xa)

(* Assumption: a < b < c *)
splay_zigzig ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Tree α
splay_zigzig a t = match t with
    | leaf         → leaf
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
                                | leaf          → leaf
                                | (al, a', ar) → (al, a', (ar, b, (br, c, cr)))
                    else leaf
            else leaf

(* TODO: Version that does not need Eq (Tree α)? *)
splay_max ∷ Eq (Tree α) ⇒ Tree α → Tree α
splay_max t = match t with
    | leaf      → leaf
    | (l, b, r) → match r with
        | leaf         → (l, b, leaf)
        | (rl, c, rr) → if rr == leaf
            then ((l, b, rl), c, leaf)
            else match splay_max rr with
                | leaf          → leaf
                | (rrl, x, xa) → (((l, b, rl), c, rrl), x, xa)

delete ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Tree α
delete a t = if t == leaf
    then leaf
    else match splay a t with
        | (l, a', r) → if a == a'
            then if l == leaf
                then r
                else match splay_max l with
                    | (l', m, r') → (l', m, r)
            else (l, a', r)

insert ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Tree α
insert a t = if t == leaf
    then (leaf, a, leaf)
    else match splay a t with
        | (l, a', r) →
            if a == a'
                then (l, a, r)
                else if a < a'
                    then (l, a, (leaf, a', r))
                    else ((l, a', leaf), a, r)

contains ∷ (Ord α, Eq (Tree α)) ⇒ α ⨯ Tree α → Bool
contains a t = match t with
  | leaf      → false
  | (l, x, r) → let ts = splay a (l, x, r) in match ts with
    | leaf          → false
    | (l2, x2, r2) → if x2 == a then true else false
