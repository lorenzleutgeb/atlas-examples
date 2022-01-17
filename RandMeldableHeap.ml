meld ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α
meld h1 h2 = match h1 with
  | leaf            → h2
  | (h1l, h1x, h1r) → match h2 with
    | leaf            → (h1l, h1x, h1r)
    | (h2l, h2x, h2r) → if h1x > h2x
      then meld (h2l, h2x, h2r) (h1l, h1x, h1r)
      else if coin
        then ((~ meld h1l (h2l, h2x, h2r)), h1x, h1r)
        else (h1l, h1x, (~ meld h1r (h2l, h2x, h2r)))

insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert x h = (meld (leaf, x, leaf) h)

del_min ∷ Ord α ⇒ α ⨯ Tree α → (Tree α ⨯ α)
del_min z h = match h with
  | leaf      → {leaf, z}
  | (l, x, r) → {(meld l r), x}

meld_noswap ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α
meld_noswap h1 h2 = match h1 with
  | leaf            → h2
  | (h1l, h1x, h1r) → match h2 with
    | leaf            → (h1l, h1x, h1r)
    | (h2l, h2x, h2r) → if h1x > h2x
      then if coin
        then ((~ meld_noswap h2l (h1l, h1x, h1r)), h2x, h2r)
        else (h2l, h2x, (~ meld_noswap h2r (h1l, h1x, h1r)))
      else if coin
        then ((~ meld_noswap h1l (h2l, h2x, h2r)), h1x, h1r)
        else (h1l, h1x, (~ meld_noswap h1r (h2l, h2x, h2r)))

