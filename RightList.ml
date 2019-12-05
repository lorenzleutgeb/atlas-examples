cons ∷ α ⨯ Tree α → Tree α
cons x t = (leaf, x, t)

(**
 * In our setting the tail of leaf is leaf.
 *)
tl ∷ Tree α → Tree α
tl t = match t with
  | leaf      → leaf
  | (l, x, r) → r

(**
 * The number of recursive calls is equivalent to
 * the "rightmost depth" of t1. We interpret t1 as
 * a list, where all elements are the right child
 * nodes, starting from t1.
 * The size of t2 is irrelevant when determining
 * the number of recursive calls to append!
 * We therefore expect cost to be expressed only
 * in some terms dependent on t1.
 *
 * This function is taken from David Obwaller's
 * mail on 2019-09-11.
 *
 * Attempt for annotation is symmetric to append_left.
 *)
append ∷ Tree α ⨯ Tree α → Tree α
append t1 t2 = match t1 with
  | leaf      → t2
  | (l, x, r) → (cons x (append r t2))

(**
 * This function is equivalent to
 *
 *     f t = leaf
 *
 * on trees, but costs the "rightmost depth"
 * of t.
 *)
descend ∷ Tree α → Tree β
descend t = match t with
  | leaf      → leaf
  | (l, m, r) → (descend r)

is ∷ Tree α → Bool
is t = match t with
  | leaf         → true
  | (lx, x, rx) → match lx with
    | leaf         → is rx
    | (ly, y, ry) → false

(**
 * This function is equivalent to
 *
 *     id x = x
 *
 * on trees, but costs the "rightmost depth"
 * of t.
 *
 * This function is taken from David Obwaller's
 * mail on 2019-09-11.
 *)
iter ∷ Tree α → Tree α
iter t = match t with
  | leaf      → leaf
  | (l, x, r) → (cons x (iter r))

(**
 * The number of recursive calls is equivalent to
 * the "leftmost depth" of t1. We interpret t1 as
 * a list, where all elements are the left child
 * nodes, starting from t1.
 * We discard r.
 * The size of t2 is irrelevant when determining
 * the number of recursive calls to rev_append!
 * We therefore expect cost to be expressed only
 * in some terms dependent on t1.
 * We think that our type system cannot solve this.
 *)
rev_append ∷ Tree α ⨯ Tree α → Tree α
rev_append t1 t2 = match t1 with
  | leaf      → t2
  | (l, x, r) → (rev_append r (cons x t2))
