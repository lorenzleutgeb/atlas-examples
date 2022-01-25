(**
 * This file was automatically generated by 'generate.sh'.
 *
 * DO NOT EDIT
 *
 * Cost for recursion : 1/3 = 1 - 2/3
 * Cost for rotation  : 2/3 = 1 - 1/3
 * Coin probability   : 1/3
 *)

splay ∷ Ord α ⇒ (α ⨯ Tree α) → Tree α
splay a t = match t with
  | node cl c cr → if a == c
    then (node cl c cr)
    else if a < c
      then match cl with
        | leaf        → (node leaf c cr)
        | node bl b br → if a == b
          then (node (node bl a br) c cr)  (* No rotation! *)
          else if a < b
            then match bl with
              | leaf → (node leaf b (node br c cr))
              | bl   → match ~ 1/3 splay a bl with
                | node al a1 ar → if coin 1/3
                  then ~ 2/3 (node al a1 (node ar b (node br c cr)))
                  else (node (node (node al a1 ar) b br) c cr)
            else match br with
              | leaf → (node bl b (node leaf c cr))
              | br   → match ~ 1/3 splay a br with
                | node al a1 ar → if coin 1/3
                  then ~ 2/3 (node (node bl b al) a1 (node ar c cr))
                  else (node (node bl b (node al a1 ar)) c cr)
      else match cr with
        | leaf        → (node cl c leaf)
        | node bl b br → if a == b
          then (node cl c (node bl a br))  (* No rotation! *)
          else if a < b
            then match bl with
              | leaf → (node (node cl c leaf) b br)
              | bl   → match ~ 1/3 splay a bl with
                | node al a1 ar → if coin 1/3
                  then ~ 2/3 (node (node cl c al) a1 (node ar b br))
                  else (node cl c (node (node al a1 ar) b br))
            else match br with
              | leaf → (node (node cl c bl) b leaf)
              | br   → match ~ 1/3 splay a br with
                | node al a1 ar → if coin 1/3
                  then ~ 2/3 (node (node (node cl c bl) b al) a1 ar)
                  else (node cl c (node bl b (node al a1 ar)))
