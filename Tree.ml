singleton ∷ α → Tree α
singleton x = (leaf, x, leaf)

singleton_let ∷ α → Tree α
singleton_let x = (let n = leaf in
  (let m = leaf in (n, x, m))
)

id ∷ Tree α → Tree α
id t = match t with
    | leaf      → leaf
    | (a, b, c) → (a, b, c)

id_match ∷ Tree α → Tree α
id_match t = match t with
    | leaf      → leaf
    | (a, b, c) → match a with
      | leaf         → (leaf, b, c)
      | (aa, ab, ac) → ((aa, ab, ac), b, c)

id_let ∷ Tree α → Tree α
id_let t = match t with
    | leaf      → leaf
    | (a, b, c) → let t' = (a, b, c) in t'

left ∷ Tree α → Tree α
left t = match t with
    | leaf      → leaf
    | (l, x, r) → l

right ∷ Tree α → Tree α
right t = match t with
    | leaf      → leaf
    | (l, x, r) → r

flip ∷ Tree α → Tree α
flip t = match t with
    | leaf      → leaf
    | (l, x, r) → (r, x, l)

empty ∷ Tree α → Bool
empty t = match t with
    | leaf      → true
    | (r, x, l) → false

clone ∷ α ⨯ Tree α → Tree α
clone x t = (t, x, t)

(**
 * Attempt to annotate:
 *   contains_unordered x t | 1 * rk(t)
 *
 * Attempt to prove:
 * Case: t == leaf
 *   rk(t)   >= 0
 *   rk(leaf) >= 0
 *   0       >= 0
 * Case: t == (l, y, r)
 *   Case: x != y
 *     Case: contains_unordered x l == true
 *       rk(t)                                 >= rk(l) + 1
 *       rk((l, y, r))                         >= rk(l) + 1
 *       rk(l) + log'(|l|) + log'(|r|) + rk(r) >= rk(l) + 1
 *               log'(|l|) + log'(|r|) + rk(r) >=         1
 * !     Error, since for l == leaf and r == leaf we have that 0 >= 1.
 *     Case: contains_unordered x l == false is symmetric.
 *   Case: x == y
 *     rk(t) >= 0
 *
 * -------------------------------------------------------------------
 *
 * Attempt to annotate:
 *   contains_unordered x t | 1 * p_{(1, 2)}
 *   ...                    | 1 * log'(1 * |t| + 2)
 *   ...                    |     log'(    |t| + 2)
 *
 * Attempt to prove:
 * Case: t == leaf
 *   log'(|t| + 2) >= 0
 *   log'(|t| + 2) >= log'(2) = 1 >= 0
 * Case: t == (l, y, r)
 *   Case: x != y
 *     Case: contains_unordered x l == true
 *       log'(|t|         + 2) >= log'(|l| + 2) + 1
 *       log'(|(l, y, r)| + 2) >= log'(|l| + 2) + 1
 *       log'(|l| + |r|   + 2) >= log'(|l| + 2) + 1
 * !     Error, since for l == leaf and r == leaf we have that 1 >= 2.
 *     Case: contains_unordered x l == false is symmetric.
 *   Case: x == y
 *     log'(|t| + 2) >= 0
 *
 * -------------------------------------------------------------------
 *
 * Attempt to annotate with new potential `ht` (short for "height"):
 *   ht(leaf)      := 1
 *   ht((l, _, r) := max({ht(l), ht(r)}) + 1
 *
 *   contains_unordered x t | ht(t)
 *
 * Attempt to prove:
 * Case: t == leaf
 *   ht(t) >= 0
 *   by definition of ht.
 * Case: t == (l, y, r)
 *   Case: x != y
 *     Case: contains_unordered x l == true
 *       ht(t) >= ht(l) + 1
 *       ht((l, y, r)) >= ht(l) + 1
 *       max({ht(l), ht(r)}) + 1 >= ht(l) + 1
 *       max({ht(l), ht(r)})     >= ht(l)
 *       Error, since for ht(r) > ht(l)
 *       Case: ht(l) >= ht(r)
 *         ht(l) >= ht(l)
 *       Case: ht(l) < ht(r)
 *         ht(r) >= ht(l)
 *   Case: x == y
 *     ht(t) >= 0
 *     by definition of ht.
 *)
contains_unordered ∷ Eq α ⇒ α ⨯ Tree α → Bool
contains_unordered x t = match t with
    | leaf      → false
    | (l, y, r) → if x == y
        then true
        else (Bool.or (contains_unordered x l) (contains_unordered x r))

(**
 * This function is equivalent to
 *
 *     id x = x
 *
 * on trees, but costs the "depth"
 * of t.
 *
 * This function is taken from David Obwaller's
 * mail on 2019-09-11.
 *
 * -------------------------------------------------------------------
 *
 * Attempt to annotate:
 *   iter_both t | 1 * rk(t)
 *
 * Attempt to prove:
 * Case: t == leaf
 *   rk(t)   >= 0
 *   rk(leaf) >= 0
 *   0       >= 0
 * Case: t == (l, x, r)
 *   rk(t)                                 >= rk((iter_both l, x, iter_both r)) + 1
 * ! Error, since we cannot expand `(iter_both l, x, iter_both r)` meaningfully.
 *)
iter ∷ Tree α → Tree α
iter t = match t with
  | leaf      → leaf
  | (l, x, r) → (iter l, x, iter r)
