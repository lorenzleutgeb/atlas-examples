descend ∷ Tree α → Tree α | [[(1 0) ↦ 1] → [], {}]
descend t = match t with
  | leaf → leaf
  | node l a r → if coin
    then node (~ descend l) a r
    else node l a (~ descend r)