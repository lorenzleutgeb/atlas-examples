meld_swap ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α
meld_swap h1 h2 = match h1 with
  | leaf             → h2
  | node h1l h1x h1r → match h2 with
    | leaf             → (node h1l h1x h1r)
    | node h2l h2x h2r → if h1x > h2x
      then meld_swap (node h2l h2x h2r) (node h1l h1x h1r)
      else if coin
        then (node (~ meld_swap h1l (node h2l h2x h2r)) h1x h1r)
        else (node h1l h1x (~ meld_swap h1r (node h2l h2x h2r)))

insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert x h = (meld (node leaf x leaf) h)

del_min ∷ Ord α ⇒ α ⨯ Tree α → (Tree α ⨯ α)
del_min z h = match h with
  | leaf       → (leaf, z)
  | node l x r → ((meld l r), x)

meld ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α
meld h1 h2 = match h1 with
  | leaf             → h2
  | node h1l h1x h1r → match h2 with
    | leaf             → (node h1l h1x h1r)
    | node h2l h2x h2r → if h1x > h2x
      then if coin
        then (node (~ meld h2l (node h1l h1x h1r)) h2x h2r)
        else (node h2l h2x (~ meld h2r (node h1l h1x h1r)))
      else if coin
        then (node (~ meld h1l (node h2l h2x h2r)) h1x h1r)
        else (node h1l h1x (~ meld h1r (node h2l h2x h2r)))
