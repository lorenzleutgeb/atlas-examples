insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert x h = (merge (node leaf x leaf) h)

delete_min ∷ Ord α ⇒ α ⨯ Tree α → (Tree α ⨯ α)
delete_min z h = match h with
  | leaf       → (leaf, z)
  | node l x r → ((merge l r), x)

merge ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α
merge h1 h2 = match h1 with
  | leaf             → h2
  | node h1l h1x h1r → match h2 with
    | leaf             → (node h1l h1x h1r)
    | node h2l h2x h2r → if h1x > h2x
      then if coin
        then (node (~ merge h2l (node h1l h1x h1r)) h2x h2r)
        else (node h2l h2x (~ merge h2r (node h1l h1x h1r)))
      else if coin
        then (node (~ merge h1l (node h2l h2x h2r)) h1x h1r)
        else (node h1l h1x (~ merge h1r (node h2l h2x h2r)))

merge_swap ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α
merge_swap h1 h2 = match h1 with
  | leaf             → h2
  | node h1l h1x h1r → match h2 with
    | leaf             → (node h1l h1x h1r)
    | node h2l h2x h2r → if h1x > h2x
      then merge_swap (node h2l h2x h2r) (node h1l h1x h1r)
      else if coin
        then (node (~ merge_swap h1l (node h2l h2x h2r)) h1x h1r)
        else (node h1l h1x (~ merge_swap h1r (node h2l h2x h2r)))

