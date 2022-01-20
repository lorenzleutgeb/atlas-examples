insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert d t = match t with
  | leaf       → node leaf d leaf
  | node l a r → if a < d
    then node (~ insert d l) a r
    else node l a (~ insert d r)

contains ∷ Ord α ⇒ α ⨯ Tree α → Bool
contains d t = match t with
  | leaf       → false
  | node l a r → if a == d
    then true
    else if a < d
      then ~ contains d l
      else ~ contains d r

delete ∷ Ord α ⇒ α ⨯ Tree α → Tree α
delete d t = match t with
  | node l a r → if a == d
    then match l with
      | leaf → r
      | l    → match rotate_max_to_root l with
        | node ll max ignore → node ll max r
    else if a < d
      then ~ delete d l
      else ~ delete d r

rotate_max_to_root ∷ Tree α → Tree α
rotate_max_to_root t = match t with
  | node l b r → match r with
    | leaf         → node l b leaf
    | node rl c rr → match rr with
      | leaf → node (node l b rl) c leaf
      | rr   → match ~ rotate_max_to_root rr with
        | node rrl1 x xa → node (node (node l b rl) c rrl1) x xa

delete_max ∷ α ⨯ Tree α → (Tree α ⨯ α)
delete_max z t = match t with
  | leaf → (leaf, z)
  | t    → match rotate_max_to_root t with
    | leaf         → (leaf, z)
    | node l max _ → (l, max)