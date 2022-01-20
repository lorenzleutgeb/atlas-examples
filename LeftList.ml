cons ∷ (α ⨯ Tree α) → Tree α
cons x t = node t x leaf

cons_cons ∷ (α ⨯ α ⨯ Tree α) → Tree α
cons_cons x y t = node (node t x leaf) y leaf

tl ∷ Tree α → Tree α
tl t = match t with
  | node l _ _ → l

(**
 * The number of recursive calls is equivalent to
 * the "leftmost depth" of t1. We interpret t1 as
 * a list, where all elements are the left child
 * nodes, starting from t1.
 * The size of t2 is irrelevant when determining
 * the number of recursive calls to append!
 * We therefore expect cost to be expressed only
 * in some terms dependent on t1.
 *)
append ∷ (Tree α ⨯ Tree α) → Tree α
append t1 t2 = match t1 with
  | leaf       → t2
  | node l x _ → (cons x (append l t2))

(**
 * This function is equivalent to
 *
 *     f t = leaf
 *
 * on trees, but costs the "leftmost depth"
 * of t.
 *)
descend ∷ Tree α → Tree β
descend t = match t with
  | node l _ _ → (descend l)

(**
 * This function is equivalent to
 *
 *     f t1 t2 = leaf
 *
 * on trees, but costs the "leftmost depth"
 * of t1.
 *)
descend_on_first ∷ (Tree α ⨯ Tree α) → Tree β
descend_on_first t1 t2 = match t1 with
  | node l x r → (descend_on_first l t2)

(**
 * This function is equivalent to
 *
 *     f t1 t2 = leaf
 *
 * on trees, but costs the "leftmost depth"
 * of t2.
 *)
descend_on_second ∷ (Tree α ⨯ Tree α) → Tree β
descend_on_second t1 t2 = match t2 with
  | node l x r → (descend_on_second t1 l)

inorder ∷ (Tree α ⨯ Tree α) → Tree α
inorder t1 t2 = match t1 with
  | leaf       → t2
  | node l x r → (inorder l (cons x (inorder r t2)))

is ∷ Tree α → Bool
is t = match t with
  | leaf       → true
  | node l _ r → match r with
    | leaf       → is l
    | node _ _ _ → false

(**
 * This function is equivalent to
 *
 *     id x = x
 *
 * on trees, but costs the "leftmost depth"
 * of t.
 *)
iter ∷ Tree α → Tree α
iter t = match t with
  | node l x r → (cons x (iter l))

postorder ∷ (Tree α ⨯ Tree α) → Tree α
postorder t1 t2 = match t1 with
  | leaf      → t2
  | node l x r → (postorder l (postorder r (cons x t2)))

preorder ∷ (Tree α ⨯ Tree α) → Tree α
preorder t1 t2 = match t1 with
  | leaf      → t2
  | node l x r → (cons x (preorder l (preorder r t2)))

(**
 * The number of recursive calls is equivalent to
 * the "leftmost depth" of t1. We interpret t1 as
 * a list, where all elements are the left child
 * nodes, starting from t1.
 * We discard r.
 * The size of t2 is irrelevant when determining
 * the number of recursive calls to append_reverse!
 * We therefore expect cost to be expressed only
 * in some terms dependent on t1.
 * We think that our type system cannot solve this.
 *)
rev_append ∷ (Tree α ⨯ Tree α) → Tree α
rev_append t1 t2 = match t1 with
  | leaf      → t2
  | node l x r → (rev_append l (cons x t2))
