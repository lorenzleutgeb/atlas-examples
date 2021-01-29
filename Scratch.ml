singleton ∷ α → Tree α
singleton x = (leaf, x, leaf)

singleton_let ∷ α → Tree α
singleton_let x = (let n = leaf in
  (let m = leaf in (n, x, m))
)

id ∷ α → α
id x = x

id_match ∷ Tree α → Tree α
id_match t = match t with
    | leaf      → leaf
    | (a, b, c) → (a, b, c)

id_match_match ∷ Tree α → Tree α
id_match_match t = match t with
    | leaf      → leaf
    | (a, b, c) → match a with
      | leaf         → (leaf, b, c)
      | (aa, ab, ac) → ((aa, ab, ac), b, c)

id_let ∷ Tree α → Tree α
id_let t = match t with
    | leaf      → leaf
    | (a, b, c) → let t1 = (a, b, c) in t1

left_child ∷ Tree α → Tree α
left_child t = match t with
    | leaf      → leaf
    | (l, x, r) → l

left ∷ α ⨯ β → α
left x y = x

right ∷ α ⨯ β → β
right x y = y

right_child ∷ Tree α → Tree α
right_child t = match t with
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

id ∷ α → α
id x = x

left ∷ α ⨯ β → α
left x y = x

right ∷ α ⨯ β → β
right x y = y

empty_1 ∷ Tree α → Bool
empty_1 t = (empty t)

empty_2 ∷ Tree α → Bool
empty_2 t = (empty_1 t)

empty_3 ∷ Tree α → Bool
empty_3 t = (let s = t in (empty s))

same_root ∷ Eq α ⇒ Tree α ⨯ Tree α → Bool
same_root t1 t2 = match t1 with
  | leaf → match t2 with
    | leaf → true
    | (t2l, t2x, t2r) → false
  | (lx, x, rx) → match t2 with
    | leaf → false
    | (ly, y, ry) → (if y == x then true else false)

empty_4 ∷ Tree α ⨯ Tree β → Bool
empty_4 t1 t2 = (Bool.or (empty t1) (empty t2))

(**
 * As of 2019-11-07 we get the following result, which looks okay:
 *
 *   same_root_obviously t | log(|t| + 2) + log(2 · |t| + 2) + 1 → 0
 *)
same_root_obviously ∷ Eq α ⇒ Tree α → Bool
same_root_obviously t = (same_root t t)

first_nonempty_and_second_empty ∷ Tree α ⨯ Tree β → Bool
first_nonempty_and_second_empty t1 t2 = match t1 with
  | leaf      → false
  | (l, x, r) → (empty t2)

(*
let_in_let_shared ∷ Tree α → Bool
let_in_let_shared t = let s = (let u = t in t) in (empty s)

let_in_let ∷ Tree α → Bool
let_in_let t = let s = (let u = t in u) in (empty s)

cf_in_cf ∷ Tree α ⨯ α ⨯ Tree α ⨯ α ⨯ Tree α → Bool
cf_in_cf t x v y w = let s = (let u = t in (u, y, w)) in (empty (s, x, v))
*)

lnf al a ar b br c cr = (let t1 = (br, c, cr) in (let t2 = (ar, b, t1) in (al, a, t2)))

lnf_raw al a ar b br c cr = (al, a, (ar, b, (br, c, cr)))

air t a = (let u = leaf in (t, a, u))

myleaf = leaf

(*
test_old t = match t with
  | leaf      → leaf
  | (l, a, r) → (l, a, (leaf, a, r))

circular t = match t with
  | leaf    → leaf
  | (l, a, r) → (let d = circular l in (d, a, r))

test t y = match t with
 | leaf      -> leaf
 | (l, a, r) -> match l with
    | leaf -> (leaf, a, r)
    | (x,b,y)-> match x with
        | leaf    -> (leaf, b,( y,a,r))
        | (k,c,l1) -> (k,c,(l1,b,(y,a,r)))

test2 t = match t with
  | leaf -> leaf
  | (l,a,r) -> match l with
     | leaf -> (leaf,a,r)
     | (x,b,y)  -> let s = test2 x in match s with
        | leaf -> (leaf,b,(y,a,r))
        | (k,c,l) -> (k,c,(l,b,(y,a,r)))

insert_test a t = match t with
  | leaf → leaf
  | (tl, ta, tr) → match SplayTree.splay a (tl, ta, tr) with
    | leaf → leaf
    | (l, a1, r) → (l, a, (leaf, a1, r))

(*
let x = leaf in
  let y = (x, a1, r) in
    (l, a, y)
*)

insert_test2 t = match t with
  | leaf → leaf
  | (l, a, r) → (l, a, (leaf, a, r))

insert_test3 a t = match SplayTree.splay a t with
  | leaf → leaf
  | (l, a1, r) → (l, a, (leaf, a1, r))

(* Works *)
insert_test4 a t = (SplayTree.splay a t)

(* Works *)
insert_test5 a t = (let d = SplayTree.splay a t in d)

*)
