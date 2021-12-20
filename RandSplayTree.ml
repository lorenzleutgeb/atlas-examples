splay a t = match t with
  | (cl, c, cr) → if a == c
    then (cl, c, cr)
    else if a < c
      then match cl with
        | leaf        → (leaf, c, cr)
        | (bl, b, br) → if a == b
          then if coin
            then (tick (bl, a, (br, c, cr)))
            else ((bl, a, br), c, cr)
          else if a < b
            then match bl with
              | leaf → (leaf, b, (br, c, cr))
              | bl   → match splay a bl with
                | leaf         → leaf
                | (al, a1, ar) → if coin
                  then (tick (al, a1, (ar, b, (br, c, cr))))
                  else (((al, a1, ar), b, br), c, cr)
            else match br with
              | leaf → (bl, b, (leaf, c, cr))
              | br   → match splay a br with
                | leaf         → leaf
                | (al, a1, ar) → if coin
                  then (tick ((bl, b, al), a1, (ar, c, cr)))
                  else ((bl, b, (al, a1, ar)), c, cr)
      else match cr with
        | leaf        → (cl, c, leaf)
        | (bl, b, br) → if a == b
          then if coin
            then (tick ((cl, c, bl), a, br))
            else (cl, c, (bl, a, br))
          else if a < b
            then match bl with
              | leaf → ((cl, c, leaf), b, br)
              | bl   → match splay a bl with
                | leaf         → leaf
                | (al, a1, ar) → if coin
                  then (tick ((cl, c, al), a1, (ar, b, br)))
                  else (cl, c, ((al, a1, ar), b, br))
            else match br with
              | leaf → ((cl, c, bl), b, leaf)
              | br   → match splay a br with
                | leaf         → leaf
                | (al, a1, ar) → if coin
                  then (tick (((cl, c, bl), b, al), a1, ar))
                  else (cl, c, (bl, b, (al, a1, ar)))
