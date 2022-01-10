f ∷ Tree α → Tree α
f t = if coin
  then ~ t
  else t

g ∷ Tree α → Tree α
g t = if coin
  then ~ 2 t
  else t

h ∷ Tree α → Tree α
h t = if coin
  then ~ 2 t
  else ~ 1 t

flip :: Tree α → Tree α
flip t = if coin
  then ~ 1 (flip t)
  else t