(**
 * Probabilistic model of SearchTree.insert
 *)
insert ∷ (α ⨯ Tree α) → Tree α
insert d t = match t with
  | leaf       → node leaf d leaf
  | node l a r → if coin (* a < d *)
    then node (~ insert d l) a r
    else node l a (~ insert d r)

(**
 * Probabilistic model of SearchTree.contains
 *)
contains ∷ Eq α ⇒ (α ⨯ Tree α) → Bool
contains d t = match t with
  | leaf       → false
  | node l a r → if a == d
    then true
    else if coin (* a < d *)
      then ~ contains d l
      else ~ contains d r

(**
 * Probabilistic model of SearchTree.delete
 *)
delete ∷ Eq α ⇒ (α ⨯ Tree α) → Tree α
delete d t = match t with
  | node l a r → if a == d
    then match l with
      | leaf → r
      | l    → match ~ SearchTree.delete_max l with
        | (ll, m) → node ll m r
    else if coin (* a < d *)
      then ~ delete d l
      else ~ delete d r