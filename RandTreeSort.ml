find ∷ Eq α ⇒ α ⨯ Tree α → Bool
find d t = match t with
  | leaf      → false
  | (l, a, r) → if a == d
    then true
    else if coin (* a < d *)
      then ~ find d l
      else ~ find d r

insert ∷ α ⨯ Tree α → Tree α
insert d t = match t with
  | leaf → (leaf, d, leaf)
  | (l, a, r) → if coin (* a < d *)
    then ((~ insert d l), a, r)
    else (l, a, (~ insert d r))

delete_max ∷ α ⨯ Tree α → (Tree α ⨯ α)
delete_max z t = match t with
  | leaf → {leaf, z}
  | t    → match rotate_max_to_root t with
    | leaf        → {leaf, z}
    | (l, max, _) → {l, max}

rotate_max_to_root ∷ Tree α → Tree α
rotate_max_to_root t = match t with
  | (l, b, r) → match r with
    | leaf        → (l, b, leaf)
    | (rl, c, rr) → match rr with
      | leaf → ((l, b, rl), c, leaf)
      | rr   → match ~ rotate_max_to_root rr with
        | (rrl1, x, xa) → (((l, b, rl), c, rrl1), x, xa)

remove ∷ Eq α ⇒ α ⨯ Tree α → Tree α
remove d t = match t with
  | (l, a, r) → if a == d
    then match l with
      | leaf → r
      | l    → match rotate_max_to_root l with
        | (ll, max, ignore) → (ll, max, r)
    else if coin (* a < d *)
      then ~ remove d l
      else ~ remove d r