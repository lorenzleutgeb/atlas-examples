neg ∷ Bool → Bool
neg x = (if x then false else true)

or ∷ Bool ⨯ Bool → Bool
or x y = (if x then true else y)

and ∷ Bool ⨯ Bool → Bool
and x y = (if x then y else false)
