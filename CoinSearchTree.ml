(**
 * A version of SearchTree, where comparison of elements α
 * is replaced by a coin flip. Thus, it does not require
 * Ord α but just Eq α.
 *)

(**
 * Probabilistic model of SearchTree.insert
 *)
insert ∷ (α ⨯ Tree α) → Tree α | [[0 ↦ 1/2, (0 2) ↦ 1/2, (1 0) ↦ 3/2] → [0 ↦ 1/2], {[(1 1) ↦ 1/2] → [(1 0) ↦ 1/2]}]
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
delete ∷ Eq α ⇒ (α ⨯ α ⨯ Tree α) → Tree α | [[0 ↦ 1/2, (0 2) ↦ 3/2, (1 0) ↦ 3/2] → [0 ↦ 1/2, (0 2) ↦ 1/2], {[] → []}]
delete z d t = match t with
  | node l a r → if a == d
    then match l with
      | leaf → r
      | l    → match ~ delete_max z l with
        | (ll, m) → node ll m r
    else if coin (* a < d *)
      then ~ (delete z d l)
      else ~ (delete z d r)

(**
 * Equal to SearchTree.delete_max, but duplicated
 * here since we want to annotate trees per module.
 *)
delete_max ∷ (α ⨯ Tree α) → (Tree α ⨯ α) | [[0 ↦ 1/2, (0 2) ↦ 1/2, (1 0) ↦ 3/2] → [0 ↦ 1/2, (0 2) ↦ 1/2], {[(1 0) ↦ 1/4] → [(1 0) ↦ 1/4]}]
delete_max z t = match t with
  | leaf       → (leaf, z)
  | node cl c cr → match cr with
    | leaf         → (cl, c)
    | node bl b br → match br with
      | leaf → ((node cl c bl), b)
      | br   → match ~ delete_max z br with
        | (t1, m) → match t1 with
          | leaf         → (leaf, z)
          | node al a ar → (node (node (node cl c bl) b al) a ar, m)
