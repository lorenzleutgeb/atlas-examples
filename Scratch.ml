id ∷ α → α
id x = x

left ∷ α ⨯ β → α
left x y = x

right ∷ α ⨯ β → β
right x y = y

empty_1 ∷ Tree α → Bool
empty_1 t = (Tree.empty t)

empty_2 ∷ Tree α → Bool
empty_2 t = (empty_1 t)

empty_3 ∷ Tree α → Bool
empty_3 t = (let s = t in (Tree.empty s))

same_root ∷ (Eq α, Eq (Tree α)) ⇒ Tree α ⨯ Tree α → Bool
same_root t1 t2 = match t1 with
  | leaf → (if t2 == leaf then true else false)
  | (lx, x, rx) → match t2 with
    | leaf → false
    | (ly, y, ry) → (if y == x then true else false)

empty_4 ∷ Tree α ⨯ Tree β → Bool
empty_4 t1 t2 = (Bool.or (Tree.empty t1) (Tree.empty t2))

(**
 * As of 2019-11-07 we get the following result, which looks okay:
 *
 *   same_root_obviously t | log(|t| + 2) + log(2 · |t| + 2) + 1 → 0
 *)
same_root_obviously ∷ (Eq α, Eq (Tree α)) ⇒ Tree α → Bool
same_root_obviously t = (same_root t t)

first_nonempty_and_second_empty ∷ Tree α ⨯ Tree β → Bool
first_nonempty_and_second_empty t1 t2 = match t1 with
  | leaf      → false
  | (l, x, r) → (Tree.empty t2)

let_in_let_shared ∷ Tree α → Bool
let_in_let_shared t = let s = (let u = t in t) in (Tree.empty s)

let_in_let ∷ Tree α → Bool
let_in_let t = let s = (let u = t in u) in (Tree.empty s)

cf_in_cf ∷ Tree α ⨯ α ⨯ Tree α ⨯ α ⨯ Tree α → Bool
cf_in_cf t x v y w = let s = (let u = t in (u, y, w)) in (Tree.empty (s, x, v))
