singleton ∷ α → Tree α
singleton x = (node leaf x leaf)

testcf ∷ Tree α ⨯ α → Tree α
testcf t x = match t with
  | leaf → (node leaf x leaf)
  | t    → t

testcf2 ∷ Tree α ⨯ α → Tree α
testcf2 y z = let x = leaf in node x z y
(*
cost: 0 -> 0
cf:
log(y+1) -> log(_)
*)

dummyx ∷ Tree α ⨯ Tree α ⨯ α → Tree α
dummyx a b z = (node a z b)
(* log(a + b - 1) -> 0 *)

testm1 ∷ Tree α ⨯ Tree α ⨯ α → Tree α
testm1 x y o = dummyx (testcf2 x o) y o
(* log(x + y) -> 0 *)

testcf3 ∷ α → Tree α
testcf3 z = let x1 = leaf in let x2 = leaf in (node x1 z x2)

singleton_let ∷ α → Tree α
singleton_let x = (let n = leaf in
  (let m = leaf in (node n x m))
)

id ∷ α → α
id x = x

id_match ∷ Tree α → Tree α
id_match t = match t with
  | node a b c → (node a b c)

id_match_match ∷ Tree α → Tree α
id_match_match t = match t with
    | node a b c → match a with
      | leaf         → (node leaf b c)
      | node aa ab ac → (node (node aa ab ac) b c)

id_let ∷ Tree α → Tree α
id_let t = match t with
    | node a b c → let t1 = (node a b c) in t1

left_child ∷ Tree α → Tree α
left_child t = match t with
    | node l x r → l

left ∷ α ⨯ β → α
left x y = x

right ∷ α ⨯ β → β
right x y = y

right_child ∷ Tree α → Tree α
right_child t = match t with
    | node l x r → r

flip ∷ Tree α → Tree α
flip t = match t with
    | node l x r → (node r x l)

empty ∷ Tree α → Bool
empty t = match t with
    | leaf      → true
    | node r x l → false

clone ∷ α ⨯ Tree α → Tree α
clone x t = (node t x t)

(**
 * Attempt to annotate:
 *   contains_unordered x t | 1 * rk(t)
 *
 * Attempt to prove:
 * Case: t == leaf
 *   rk(t)   >= 0
 *   rk(leaf) >= 0
 *   0       >= 0
 * Case: t == (node l y r)
 *   Case: x != y
 *     Case: contains_unordered x l == true
 *       rk(t)                                 >= rk(l) + 1
 *       rk((node l y r))                         >= rk(l) + 1
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
 * Case: t == (node l y r)
 *   Case: x != y
 *     Case: contains_unordered x l == true
 *       log'(|t|         + 2) >= log'(|l| + 2) + 1
 *       log'(|(node l y r)| + 2) >= log'(|l| + 2) + 1
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
 * Case: t == (node l y r)
 *   Case: x != y
 *     Case: contains_unordered x l == true
 *       ht(t) >= ht(l) + 1
 *       ht((node l y r)) >= ht(l) + 1
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
    | node l y r → if x == y
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
 * Case: t == (node l x r)
 *   rk(t)                                 >= rk((iter_both l, x, iter_both r)) + 1
 * ! Error, since we cannot expand `(iter_both l, x, iter_both r)` meaningfully.
 *)
iter ∷ Tree α → Tree α
iter t = match t with
  | node l x r → (node (iter l) x (iter r))

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
    | node t2l t2x t2r → false
  | node lx x rx → match t2 with
    | leaf → false
    | node ly y ry → (if y == x then true else false)

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
  | node l x r → (empty t2)

(*
let_in_let_shared ∷ Tree α → Bool
let_in_let_shared t = let s = (let u = t in t) in (empty s)

let_in_let ∷ Tree α → Bool
let_in_let t = let s = (let u = t in u) in (empty s)

cf_in_cf ∷ Tree α ⨯ α ⨯ Tree α ⨯ α ⨯ Tree α → Bool
cf_in_cf t x v y w = let s = (let u = t in (node u y w)) in (empty (node s x v))
*)

lnf al a ar b br c cr = (let t1 = (node br c cr) in (let t2 = (node ar b t1) in (node al a t2)))

lnf_raw al a ar b br c cr = (node al a (node ar b (node br c cr)))

air t a = (let u = leaf in (node t a u))

myleaf = leaf

(*
test_old t = match t with
  | node l a r → (node l a (node leaf a r))

circular t = match t with
  | node l a r → (let d = circular l in (node d a r))

test t y = match t with
 | node l a r → match l with
    | leaf    → (node leaf a r)
    | node x b y → match x with
        | leaf     → (node leaf b (node y a r))
        | node k c l1 → (node k c (node l1 b (node y a r)))

test2 t = match t with
  | node l a r → match l with
     | leaf    → (node leaf a r)
     | node x b y → let s = test2 x in match s with
        | leaf    → (node leaf b (node y a r))
        | node k c l → (node k c (node l b (node y a r)))

insert_test a t = match t with
  | node tl ta tr → match SplayTree.splay a (node tl ta tr) with
    | node l a1 r → (node l a (node leaf a1 r))

(*
let x = leaf in
  let y = (node x a1 r) in
    (node l a y)
*)

insert_test2 t = match t with
  | node l a r → (node l a (node leaf a r))

insert_test3 a t = match SplayTree.splay a t with
  | node l a1 r → (node l a (node leaf a1 r))

(* Works *)
insert_test4 a t = (SplayTree.splay a t)

(* Works *)
insert_test5 a t = (let d = SplayTree.splay a t in d)

*)

f2 ∷ Tree α → Tree α
f2 t = match t with
  | node tl x tr → let t1 ≔ ~ 1 2 (f2 tl) in t1

(**
 * NOTE: Terminates only on `leaf`, but does not terminate on any other tree!
 *)
f3 ∷ Tree α → Tree α
f3 t = match t with
  | t    → let t1 ≔ ~ 1 2 (f3 t) in t1

(**
 * NOTE: Does not terminate.
 *)
f4 ∷ Tree α → Tree α
f4 t = let t1 ≔ ~ 1 2 (f4 t) in t1

f5 ∷ Tree α * α → Tree α
f5 t a = match t with
  | leaf        → (node leaf a leaf)
  | node tl x tr → ~ 1 2 (f5 tl a)

f6 ∷ Tree α * α → Tree α
f6 t a = match t with
  | leaf        → (node leaf a leaf)
  | node tl x tr → ~ 1 2 let t1 ≔ f6 tl a in t1

f7 ∷ Tree α * α → Tree α
f7 t a = match t with
  | leaf        → (node leaf a leaf)
  | node tl x tr → let t1 ≔ ~ 1 2 (f7 tl a) in t1

h ∷ Tree α → Tree α
h t = let t1 ≔ ~ 1 2 (h t) in t1

id1 ∷ Tree α → Tree α
id1 t = t

id2 ∷ Tree α → Tree α
id2 t = id1 t

id3 ∷ Tree α → Tree α
id3 t = ~ id1 t

id4 ∷ Tree α → Tree α
id4 t = let d ≔ ~ id1 t in d

test ∷ Tree α ⨯ Tree α ⨯ Tree α ⨯ α → Tree α
test a b c dummy = let c1 = id1 c in (node (node (node c1 dummy b) dummy a) dummy leaf)

test5 ∷ Tree α ⨯ Tree α ⨯ Tree α ⨯ α → Tree α
test5 a b c dummy = let c1 = id1 c in (node (node c1 dummy b) dummy a)

test6 ∷ Tree α ⨯ Tree α ⨯ α → Tree α
test6 b c dummy = let c1 = id1 c in (node c1 dummy b)

test7 ∷ Tree α ⨯ Tree α ⨯ Tree α ⨯ α → Tree α
test7 a b c dummy = let c1 = id1 c in (node c1 dummy b)

test2 ∷ Tree α ⨯ Tree α ⨯ α → Tree α
test2 b c dummy = let c1 = id1 c in (node (node c1 dummy b) dummy leaf)

test3 ∷ Tree α ⨯ α → Tree α
test3 c dummy = let c1 = id1 c in (node c1 dummy leaf)

test4 ∷ Tree α ⨯ α → Tree α
test4 c dummy = (node c dummy leaf)

test8 ∷ Tree α ⨯ α → Tree α
test8 t dummy = (node (node leaf dummy leaf) dummy t)

test9 ∷ Tree α ⨯ Tree α ⨯ α → Tree α
test9 t1 t2 dummy = (node (node leaf dummy leaf) dummy (node t1 dummy t2))

insert_zigzig ∷ α ⨯ Tree α → Tree α
insert_zigzig a t = match t with
   | leaf → leaf
   | node cl c cr → (* assume a < c *) match cl with
     | leaf        → (node (node leaf a leaf) c cr)
     | node bl b br → (* assume a < b *) match bl with
       | leaf → (node (node leaf a leaf) b (node br c cr))
       | bl   → match (~ 1 2 (insert_dummy bl)) with
         | node al a1 ar → if coin
           then (~ 1 2 (node al a1 (node ar b (node br c cr))))
           else (node (node (node al a1 ar) b br) c cr)

insert_zigzag ∷ α ⨯ Tree α → Tree α
insert_zigzag a t = match t with
  | leaf → leaf
  | node cl c cr → (* assume a < c *) match cl with
    | leaf        → (node leaf (*node leaf a leaf*) c cr)
    | node bl b br → (* assume !(a < b) *) match br with
      | leaf → (node bl b (node leaf (*node leaf, a, leaf*) c cr))
      | br   → match ~ 1 2 insert_zigzag a br with
        | leaf         → leaf
        | node al a1 ar → if coin
          then ~ 1 2 (node (node bl b al) a1 (node ar c cr))
          else (node (node bl b (node al a1 ar)) c cr)

insert_dummy ∷ Tree α → Tree α
insert_dummy t = t

goal_dummy ∷ Tree α ⨯ Tree α ⨯ Tree α ⨯ α → Tree α
goal_dummy bl br cr c = (node (node bl c br) c cr)

insert_coin ∷ Eq α ⇒ α ⨯ Tree α → Tree α
insert_coin a t = match t with
  | node cl c cr → if a == c
    then (node cl c cr)
    else match cl with
  | leaf        → (node (node leaf a leaf) c cr)
  | node bl b br → if a == b
    then (node (node bl a br) c cr) (* Found. No rotation. *)
    else match br with
      | leaf → (node bl a (node (node leaf a leaf) c cr))
      | br   →  match ~ 1 2 insert_dummy br with
        | node al a1 ar → if coin
          then ~ 1 2 (node (node bl a1 al) a1 (node ar c cr))
          else (node (node bl a1 (node al a1 ar)) c cr)

insert_zigzig_coin ∷ Tree α ⨯ α ⨯ Tree α ⨯ α ⨯ Tree α ⨯ α ⨯ Tree α → Tree α
insert_zigzig_coin al a ar b br c cr = if coin
      then ~ 1 2 (node al a (node ar b (node br c cr)))
      else (node (node (node al a ar) b br) c cr)

insert_zigzig_rec ∷ α ⨯ Tree α ⨯ α ⨯ Tree α ⨯ α ⨯ Tree α → Tree α
insert_zigzig_rec a bl b br c cr = match ~ 1 2 insert_dummy bl with
  | node al a1 ar → if coin
    then ~ 1 2 (node al a1 (node ar b (node br c cr)))
    else (node (node (node al a1 ar) b br) c cr)

insert_zigzig_match ∷ α ⨯ Tree α ⨯ α ⨯ Tree α ⨯ α ⨯ Tree α → Tree α
insert_zigzig_match a bl b br c cr = match bl with
  | leaf → (node (node leaf a leaf) b (node br c cr))
  | bl   → match ~ 1 2 insert_dummy bl with
    | node al a1 ar → if coin
      then ~ 1 2 (node al a1 (node ar b (node br c cr)))
      else (node (node (node al a1 ar) b br) c cr)

insert_zigzig_match_cl ∷ Eq α ⇒ α ⨯ Tree α ⨯ α ⨯ Tree α → Tree α
insert_zigzig_match_cl a cl c cr = match cl with
  | leaf        → leaf (*node (node leaf a leaf) c cr*)
  | node bl b br → if a == b
    then leaf (*node (node bl a br) c cr*) (* Found. No rotation. *)
    else match bl with
      | leaf → (node (node leaf a leaf) b (node br c cr))
      | bl   → match ~ 1 2 insert_dummy bl with
        | node al a1 ar → if coin
          then ~ 1 2 (node al a1 (node ar b (node br c cr)))
          else (node (node (node al a1 ar) b br) c cr)

insert_zigzig_match_t_empty ∷ Eq α ⇒ α ⨯ Tree α → Tree α
insert_zigzig_match_t_empty a t = match t with
  | node cl c cr → match cl with
    | leaf        → (node (node leaf a leaf) c cr)
    | node bl b br → if a == b
      then (node (node bl a br) c cr) (* Found. No rotation. *)
      else insert_zigzig_match a bl b br c cr (*goal_dummy bl br cr c*)

insert_zigzig_match_t ∷ Eq α ⇒ α ⨯ Tree α → Tree α
insert_zigzig_match_t a t = match t with
  | node cl c cr → (*if a == c
    then (node cl c cr)
    else *) match cl with
  | leaf        → (node (node leaf a leaf) c cr)
  | node bl b br → if a == b
    then (node (node bl a br) c cr) (* Found. No rotation. *)
    else match bl with
      | leaf → (node (node leaf a leaf) b (node br c cr))
      | bl   → match ~ 1 2 insert_dummy bl with
        | node al a1 ar → if coin
          then ~ 1 2 (node al a1 (node ar b (node br c cr)))
          else (node (node (node al a1 ar) b br) c cr)

insert_zigzag_match_cl ∷ α ⨯ Tree α ⨯ α ⨯ Tree α → Tree α
insert_zigzag_match_cl a cl c cr = match cl with
    | leaf        → (node (node leaf a leaf) c cr)
    | node bl b br → (* assume !(a < b) *) match br with
      | leaf → (node bl b (node (node leaf a leaf) c cr))
      | br   → match ~ 1 2 insert_zigzag a br with
        | leaf         → leaf
        | node al a1 ar → if coin
          then ~ 1 2 (node (node bl b al) a1 (node ar c cr))
          else (node (node bl b (node al a1 ar)) c cr)
