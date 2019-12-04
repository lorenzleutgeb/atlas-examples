del_min ∷ Ord α ⇒ Tree α → Tree α
del_min t = match t with
  | nil       → nil
  | (l, m, r) → (merge l r)

insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert a h = (merge (nil, a, nil) h)
(* insert a h = (merge (Tree.singleton a) h) *)

merge ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α
merge h1 h2 = match h1 with
  | nil          → h2
  | (l1, a1, r1) → match h2 with
    | nil          → (l1, a1, r1)
    | (l2, a2, r2) → if a1 < a2
      then ((merge (l2, a2, r2) r1), a1, l1)
      else ((merge (l1, a1, r1) r2), a2, l2)
