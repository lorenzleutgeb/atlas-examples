(**
 * Definitions that do not assume/preserve ordering.
 *)

id ∷ Tree α → Tree α
id x = x

singleton ∷ α → Tree α
singleton x = node leaf x leaf

iter ∷ Tree α → Tree α
iter t = match t with
  | node l x r → node (iter l) x (iter r)

left ∷ Tree α → Tree α
left t = match t with
  | node l _ _ → l

right ∷ Tree α → Tree α
right t = match t with
  | node _ _ r → r

flip ∷ Tree α → Tree α
flip t = match t with
  | node l x r → node r x l

clone ∷ (α ⨯ Tree α) → Tree α
clone x t = node t x t

empty ∷ Tree α → Bool
empty t = match t with
  | leaf       → true
  | node r x l → false

contains ∷ Eq α ⇒ (α ⨯ Tree α) → Bool
contains x t = match t with
  | leaf       → false
  | node l y r → if x == y
    then true
    else (Bool.or (contains x l) (contains x r))
