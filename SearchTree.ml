insert ∷ Ord α ⇒ (α ⨯ Tree α) → Tree α
insert d t = match t with
  | leaf       → node leaf d leaf
  | node l a r → if a < d
    then node (~ insert d l) a r
    else node l a (~ insert d r)

contains ∷ Ord α ⇒ (α ⨯ Tree α) → Bool
contains d t = match t with
  | leaf       → false
  | node l a r → if a == d
    then true
    else if a < d
      then ~ contains d l
      else ~ contains d r

delete ∷ Ord α ⇒ (α ⨯ α ⨯ Tree α) → Tree α
delete z d t = match t with
  | node l a r → if a == d
    then match l with
      | leaf → r
      | l    → match ~ SearchTree.delete_max z l with
        | (ll, m) → node ll m r
    else if a < d
      then ~ delete d l
      else ~ delete d r

delete_max ∷ (α ⨯ Tree α) → (Tree α ⨯ α)
delete_max z t = match t with
  | leaf       → (leaf, z)
  | node cl c cr → match cr with
    | leaf         → (cl, c)
    | node bl b br → match br with
      | leaf → ((node cl c bl), b)
      | br   → match ~ delete_max br with
        | (t', m) → match t' with
          | leaf         → (leaf, z)
          | node al a ar → (node (node (node cl c bl) b al) a ar, m)