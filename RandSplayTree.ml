splay ∷ Ord α ⇒ (α ⨯ Tree α) → Tree α
splay a t = match t with
  | node cl c cr → if a == c
    then (node cl c cr)
    else if a < c
      then match cl with
        | leaf         → node leaf c cr
        | node bl b br → if a == b
          then node (node bl a br) c cr  (* No rotation! *)
          else if a < b
            then match bl with
              | leaf → node leaf b (node br c cr)
              | bl   → match ~ 1/2 splay a bl with
                | node al _ ar → if coin
                  then ~ 1/2 node al a (node ar b (node br c cr))
                  else       node (node (node al a ar) b br) c cr
            else match br with
              | leaf → (node bl b (node leaf c cr))
              | br   → match ~ 1/2 splay a br with
                | node al _ ar → if coin
                  then ~ 1/2 node (node bl b al) a (node ar c cr)
                  else       node (node bl b (node al a ar)) c cr
      else match cr with
        | leaf        → (node cl c leaf)
        | node bl b br → if a == b
          then (node cl c (node bl a br))  (* No rotation! *)
          else if a < b
            then match bl with
              | leaf → (node (node cl c leaf) b br)
              | bl   → match ~ 1/2 splay a bl with
                | node al _ ar → if coin
                  then ~ 1/2 node (node cl c al) a (node ar b br)
                  else       node cl c (node (node al a ar) b br)
            else match br with
              | leaf → (node (node cl c bl) b leaf)
              | br   → match ~ 1/2 splay a br with
                | node al _ ar → if coin
                  then ~ 1/2 node (node (node cl c bl) b al) a ar
                  else       node cl c (node bl b (node al a ar))

insert ∷ Ord α ⇒ (α ⨯ Tree α) → Tree α
insert a t = match t with
  | node cl c cr → if a == c
    then (node cl c cr)
    else if a < c
      then match cl with
        | leaf         → node (node leaf a leaf) c cr
        | node bl b br → if a == b
          then node (node bl a br) c cr (* Found. No rotation. *)
          else if a < b
            then match bl with
              | leaf → node (node leaf a leaf) b (node br c cr)
              | bl   → match ~ 1/2 insert a bl with
                | node al _ ar → if coin
                  then ~ 1/2 node al a (node ar b (node br c cr))
                  else       node (node (node al a ar) b br) c cr
            else match br with
              | leaf → node bl b (node (node leaf a leaf) c cr)
              | br   → match ~ 1/2 insert a br with
                | node al _ ar → if coin
                  then ~ 1/2 node (node bl b al) a (node ar c cr)
                  else       node (node bl b (node al a ar)) c cr
      else match cr with
        | leaf         → node cl c (node leaf a leaf)
        | node bl b br → if a == b
          then node cl c (node bl a br) (* Found. No rotation. *)
          else if a < b
            then match bl with
              | leaf → node (node cl c (node leaf a leaf)) b br
              | bl   → match ~ 1/2 insert a bl with
                | node al _ ar → if coin
                  then ~ 1/2 node (node cl c al) a (node ar b br)
                  else       node cl c (node (node al a ar) b br)
            else match br with
              | leaf → node (node cl c bl) b (node leaf a leaf)
              | br   → match ~ 1/2 insert a br with
                | node al _ ar → if coin
                  then ~ 1/2 node (node (node cl c bl) b al) a ar
                  else       node cl c (node bl b (node al a ar))

splay_max ∷ (α ⨯ Tree α) → (Tree α ⨯ α)
splay_max z t = match t with
  | leaf      → (leaf, z)
  | node l b r → match r with
    | leaf        → (node l b leaf, b)
    | node rl c rr → match rr with
      | leaf → (node (node l b rl) c leaf, c)
      | rr   → match ~ 1/2 splay_max z rr with
        | (r1, max) → match r1 with
          | leaf          → (leaf, z)
          | node rrl1 x xa → if coin
            then ~ 1/2 (node (node (node l b rl) c rrl1) x xa, max)
            else       (node l b (node rl c (node rrl1 x xa)), max) (* No rotation! *)

delete ∷ Ord α ⇒ (α ⨯ α ⨯ Tree α) → Tree α
delete z a t = match t with
  | node cl c cr → if a == c
    then match splay_max z cl with
      | (cl1, max) → node cl1 max cr
    else if a < c
      then match cl with
        | leaf         → node leaf c cr
        | node bl b br → if a == b
          then match splay_max z bl with
            | (bl1, max) → node (node bl1 max br) c cr
          else if a < b
            then match bl with
              | leaf → node leaf b (node br c cr)
              | bl   → match ~ 1/2 delete z a bl with
                | node al _ ar → if coin
                  then ~ 1/2 node al a (node ar b (node br c cr))
                  else       node (node (node al a ar) b br) c cr
            else match br with
              | leaf → node bl b (node leaf c cr)
              | br   → match ~ 1/2 delete z a br with
                | node al _ ar → if coin
                  then ~ 1/2 node (node bl b al) a (node ar c cr)
                  else       node (node bl b (node al a ar)) c cr
      else match cr with
        | leaf         → node cl c leaf
        | node bl b br → if a == b
          then match splay_max z bl with
            | (bl1, max) → node cl c (node bl1 max br)
          else if a < b
            then match bl with
              | leaf → node (node cl c leaf) b br
              | bl   → match ~ 1/2 delete z a bl with
                | node al _ ar → if coin
                  then ~ 1/2 node (node cl c al) a (node ar b br)
                  else       node cl c (node (node al a ar) b br)
            else match br with
              | leaf → node (node cl c bl) b leaf
              | br   → match ~ 1/2 delete z a br with
                | node al _ ar → if coin
                  then ~ 1/2 node (node (node cl c bl) b al) a ar
                  else       node cl c (node bl b (node al a ar))
