(*
 (**
  * NOTE: All of this file is commented, since it contains syntax that cannot be
  * parsed with current implementations, such as higher order functions and
  * trees containing booleans.
  * If you want to try it out, remove the outermost comment (in the first and
  * last line of this file).
  *)

and ∷ Tree Bool → Bool
and t =
  match t with
    | leaf → true
    | node l x r →
      if and l
        then if x then and r
                  else false
        else false;

or ∷ Tree Bool → Bool
or t =
  match t with
    | leaf → false
    | node l x r →
      if or l then true
              else if x then true
                        else or r;

any ∷ (α → Bool) ⨯ Tree α → Bool
any f t = or (map f t);

all ∷ (α → Bool) ⨯ Tree α → Bool
all f t = and (map f t);

map ∷ (α → β) ⨯ Tree α → Tree β
map f t =
  match t with
    | node l x r → (node (map f l) (f x) (map f r));

fold ∷ (β * α → β) * β ⨯ Tree α → β
fold f z t =
  match t with
    | leaf → z
    | node l x r → f (f (fold f z l) x) (fold f z t);

zipWith ∷ (a * β → γ) ⨯ Tree α ⨯ Tree β → Tree γ
zipWith f t u =
  match t with
    | node l x r →
        match u with
          | node v y w → let l' = zipWith f l v in
                         let r' = zipWith f r w in
                         (node l' (f x y) r');

n1 ∷ (α → Tree β) * a * β ⨯ Tree β → Tree β
n1 f x y z =
  let l = f x in
  let r = (node l y z)
  in
  (node l y z);

*)
