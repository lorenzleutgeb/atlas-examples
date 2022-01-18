descend ∷ Tree α → Tree α
descend t = match t with
  | leaf → leaf
  | node l a r → if coin
    then node (~ descend l) a r
    else node l a (~ descend r)

find ∷ Eq α ⇒ α ⨯ Tree α → Bool
find d t = match t with
  | leaf       → false
  | node l a r → if a == d
    then true
    else if coin (* a < d *)
      then ~ find d l
      else ~ find d r

insert ∷ α ⨯ Tree α → Tree α
insert d t = match t with
  | leaf       → node leaf d leaf
  | node l a r → if coin (* a < d *)
    then node (~ insert d l) a r
    else node l a (~ insert d r)

delete_max ∷ α ⨯ Tree α → (Tree α ⨯ α)
delete_max z t = match t with
  | leaf → (leaf, z)
  | t    → match rotate_max_to_root t with
    | leaf         → (leaf, z)
    | node l max _ → (l, max)

rotate_max_to_root ∷ Tree α → Tree α
rotate_max_to_root t = match t with
  | node l b r → match r with
    | leaf         → node l b leaf
    | node rl c rr → match rr with
      | leaf → node (node l b rl) c leaf
      | rr   → match ~ rotate_max_to_root rr with
        | node rrl1 x xa → node (node (node l b rl) c rrl1) x xa

remove ∷ Eq α ⇒ α ⨯ Tree α → Tree α
remove d t = match t with
  | node l a r → if a == d
    then match l with
      | leaf → r
      | l    → match rotate_max_to_root l with
        | node ll max ignore → node ll max r
    else if coin (* a < d *)
      then ~ remove d l
      else ~ remove d r