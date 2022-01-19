(**
 * The function definitions in this file are taken from or made to match
 * Section 8 of
 *
 *   Tobias Nipkow, Hauke Brinkop
 *   Amortized Complexity Verified
 *   Journal of Automated Reasoning, Vol. 62, Iss. 3, pp. 367-391
 *   https://doi.org/10.1007/s10817-018-9459-3
 *)

(**
 * Exposed definitions are
 *  - insert
 *  - delete_min
 *)

(**
 * Original definition:
 *
 *   is_root h = (case h of leaf → true | node l x r → r == leaf)
 *)
is_root ∷ Tree α → Bool
is_root h = match h with
  | leaf      → true
  | node _ _ r → match r with
    | leaf → true
    | _    → false

(**
 * Original definition:
 *
 *   pheap leaf = true
 *   pheap (node l x r) = (pheap l /\ pheap r /\ (\forall y \in set_tree l. x <= y))
 *)
pheap ∷ Ord α ⇒ Tree α → Bool
pheap h = match h with
  | leaf → true
  | node l x r → (Bool.and (Bool.and (~ pheap l) (~ pheap r)) (~ all_leq l x))

all_leq ∷ Ord α ⇒ Tree α ⨯ α → Bool
all_leq t x = match t with
  | leaf → true
  | node l y r → if y > x
    then false
    else (Bool.and (~ all_leq l x) (~ all_leq r x))

(**
 * Original definition:
 *
 *   link leaf = leaf
 *   link (node lx x leaf) = (node lx x leaf)
 *   link (node lx x (node ly y ry)) = (if x < y then (node (node ly y lx) x ry) else (node (node lx x ly) y ry))
 *)
link ∷ Ord α ⇒ Tree α → Tree α
link h = match h with
  | node lx x rx → match rx with
    | leaf        → (node lx x leaf)
    | node ly y ry → if x < y
      then (node (node ly y lx) x ry)
      else (node (node lx x ly) y ry)

insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α | [[0 ↦ 1, (1 2) ↦ 6] → [0 ↦ 1, (0 2) ↦ 1], {}]
insert x h = (merge (node leaf x leaf) h)

insert_isolated ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert_isolated x h = match h with
  | leaf       → (node leaf x leaf)
  | node ly y _ → if x < y
    then (node (node ly y leaf) x leaf)
    else (node (node leaf x ly) y leaf)

(**
 * Original definition:
 *
 *   merge leaf h = h
 *   merge h leaf = h
 *   merge (node lx x leaf) (node ly y leaf) = link (node lx x (node ly y leaf))
 *
 * But note that we cannot restrict ourselves to the arguments having
 * a right-subtree equal to leaf.
 *
 * Proof of a logarithmic upper bound for merge, in analogy to Lemma 8.4:
 *
 * As potential function we take:
 *
 *   Phi leaf      := 0
 *   Phi (node l _ r) := Phi l + Phi r + log' |l| + log' |r|
 *
 * where
 *
 *   |leaf| := 1    and    |node l _ r| := |l| + |r|
 *
 * Let h1 := (node lx x leaf) and h2 := (node ly y leaf)
 *
 * We want to show
 *
 *   Phi (merge h1 h2) - (Phi h1 + Phi h2) =
 *   Phi (merge h1 h2) -  Phi h1 - Phi h2  <=
 *   log' (|h1| + |h2|)
 *
 * First, observe following equality
 *
 *     Phi (merge h1 h2)
 *   = Phi (link (node lx x h2))                                       (def. merge)
 *   = Phi (node (node ly y lx) x leaf)                                    (w.l.o.g. by def. link)
 *   = Phi (node ly y lx) + Phi leaf + log' |(node ly y lx)| + log' |leaf|  (def. Phi)
 *   = Phi (node ly y lx) + 0       + log' |(node ly y lx)| + 0           (def. Phi, |_|)
 *   = Phi (node ly y lx) + log' (|ly| + |lx|)                         (def. |_|)
 *   = Phi ly + Phi lx + log' |lx| + log' |ly| + log' (|ly| + |lx|) (def. Phi)
 *
 * Then, it follows that
 *
 *      Phi (merge h1 h2) - Phi h1 - Phi h2
 *    = Phi ly + Phi lx + log' |lx| + log' |ly| + log' (|ly + |lx|) (def. Phi)
 *    - Phi lx - Phi leaf - log' |lx| - log' |leaf|
 *    - Phi ly - Phi leaf - log' |ly| - log' |leaf|
 *    = ~                                                           (def. Phi, |_|)
 *    - Phi lx - 0       - log' |lx| - 0
 *    - Phi ly - 0       - log' |ly| - 0
 *    = log' (|ly| + |lx|)
 *   <= log' (|lx| + |ly| + 2)                    (monotone log')
 *    = log' (|lx| + |leaf| + |ly| + |leaf|)
 *    = log' (|h1| + |h2|)
 *
 * For the more general case:
 *
 * Let h1 := (node lx x rx) and h2 := (node ly y ry)
 *
 * We want to show
 *
 *   Phi (merge h1 h2) - (Phi h1 + Phi h2) =
 *   Phi (merge h1 h2) -  Phi h1 - Phi h2  <=
 *   log' (|h1| + |h2|)
 *
 * First, observe following equality
 *
 *     Phi (merge h1 h2)
 *   = Phi (link (node lx x (node ly y leaf)))    (def. merge)
 *   Case x < y:
 *     = Phi (node (node ly y lx) x leaf)                                    (def. link)
 *     = Phi (node ly y lx) + Phi leaf + log' |(node ly y lx)| + log' |leaf|  (def. Phi)
 *     = Phi (node ly y lx) + 0       + log' (|ly| + |lx|) + 0           (def. Phi, |_|)
 *     = Phi ly + Phi lx + log' |lx| + log' |ly| + log' (|ly| + |lx|) (def. Phi)
 *   Case x >= y:
 *     = Phi (node (node lx x ly) y leaf)                                    (def. link)
 *     = Phi (node lx x ly) + Phi leaf + log' |(node lx x ly)| + log' |leaf|  (def. Phi)
 *     = Phi (node lx x ly) + 0       + log' (|lx| + |ly|) + 0           (def. Phi, |_|)
 *     = Phi lx + Phi ly + log' |ly| + log' |lx| + log' (|lx| + |ly|) (def. Phi)
 *   = Phi lx + Phi ly + log' |lx| + log' |ly| + log' (|lx| + |ly|) (comm. +)
 *
 * Then, it follows that
 *
 *      Phi (merge h1 h2) - Phi h1 - Phi h2
 *    = Phi lx + Phi ly + log' |lx| + log' |ly| + log' (|lx + |ly|) (def. Phi)
 *    - Phi lx - Phi rx - log' |lx| - log' |rx|
 *    - Phi ly - Phi ry - log' |ly| - log' |ry|
 *    = log' (|ly| + |lx|) - Phi rx - log' |rx| - Phi ry - log' |ry|
 *   <= log' (|ly| + |lx|)                       (log' |_| >= 0, Phi _ >= 0, def. -)
 *   <= log' (|lx| + |rx| + 1 + |ly| + |ry| + 1) (monotone log'))
 *    = log' (|h1| + |h2|)
 *)
merge ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α | [[0 ↦ 1, 1 ↦ 1, (0 0 2) ↦ 4, (1 1 0) ↦ 2] → [0 ↦ 1, (0 2) ↦ 2], {[] → []}]
merge h1 h2 = match h1 with
  | leaf        → h2
  | node lx x rx → match h2 with
    | leaf        → (node lx x rx)
    | node ly y ry → (link (node lx x (node ly y leaf)))

(**
 * Here, link is inlined. Since `merge` calls `leaf`
 * on `(lx, x, (node ly y leaf))` one can directly
 * inline the node-branch of the second match
 * in the definition of link, i.e.
 *
 *   link (node lx x (node ly y leaf)) = if x < y
 *       then (node (node ly y lx) x leaf)
 *       else (node (node lx x ly) y leaf)
 *)
merge_isolated ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α | [[0 ↦ 1 / 2, 1 ↦ 1 / 2, (0 0 2) ↦ 2, (1 1 0) ↦ 1 / 2] → [0 ↦ 1 / 2, (0 2) ↦ 1], {[] → []}]
merge_isolated h1 h2 = match h1 with
  | leaf        → h2
  | node lx x rx → match h2 with
    | leaf        → (node lx x rx)
    | node ly y ry → if x < y
      then (node (node ly y lx) x leaf)
      else (node (node lx x ly) y leaf)

delete_min ∷ Ord α ⇒ Tree α → Tree α
delete_min h = match h with
  | node l _ _ → (~ pass2 (~ pass1 l))

(* Same as `delete_min` but with `merge_pairs_isolated` instead of `pass1` and `pass2`. *)
delete_min_via_merge_pairs_isolated ∷ Ord α ⇒ Tree α → Tree α
delete_min_via_merge_pairs_isolated h = match h with
  | node l _ _ → ~ merge_pairs_isolated l

delete_min_via_merge_pairs ∷ Ord α ⇒ Tree α → Tree α
delete_min_via_merge_pairs h = match h with
  | node l _ _ → ~ merge_pairs l

pass1 ∷ Ord α ⇒ Tree α → Tree α | [[0 ↦ 3, (0 2) ↦ 1, (1 0) ↦ 2] → [0 ↦ 1, (0 2) ↦ 1, (1 0) ↦ 1], {[(1 0) ↦ 2] → [(1 0) ↦ 2], [(1 0) ↦ 2, (1 1) ↦ 2, (1 2) ↦ 2] → [(1 0) ↦ 2], [(1 0) ↦ 1] → [(1 0) ↦ 1], [] → []}]
pass1 h = match h with
  | node lx x rx → match rx with
    | leaf        → (node lx x leaf)
    | node ly y ry → (~ link (node lx x (node ly y (~ pass1 ry))))

pass2 ∷ Ord α ⇒ Tree α → Tree α | [[0 ↦ 3, (0 2) ↦ 1, (1 0) ↦ 4] → [0 ↦ 1, (0 2) ↦ 1, (1 0) ↦ 1], {[(1 0) ↦ 2] → [(1 0) ↦ 2], [] → [], [(1 0) ↦ 2, (1 1) ↦ 2, (1 2) ↦ 2] → [(1 0) ↦ 2]}]
pass2 h = match h with
  | node l x r → (~ link (node l x (~ pass2 r)))

merge_pairs ∷ Ord α ⇒ Tree α → Tree α
merge_pairs h = match h with
  | node lx x rx → match rx with
    | leaf        → (node lx x leaf)
    | node ly y ry → (~ link (~ link (node lx x (node ly y (~ merge_pairs ry)))))

(* The same as `merge_pairs` but with `link` inlined. *)
merge_pairs_isolated ∷ Ord α ⇒ Tree α → Tree α | [[0 ↦ 1, (0 2) ↦ 1, (1 0) ↦ 3] → [0 ↦ 1, (0 2) ↦ 1], {[] → [], [(1 0) ↦ 1] → [(1 0) ↦ 1]}]
merge_pairs_isolated h = match h with
  | node la a ra → match ra with
    | leaf        → (node la a leaf)
    | node lb b rb → match ~ merge_pairs_isolated rb with
      | leaf → if a < b
        then (node (node lb b la) a leaf)
        else (node (node la a lb) b leaf)
      | node lc c rc → if a < b
        then if a < c
          then (node (node lc c (node lb b la)) a rc)
          else (node (node (node lb b la) a lc) c rc)
        else if b < c
          then (node (node lc c (node la a lb)) b rc)
          else (node (node (node la a lb) b lc) c rc)

merge_pairs_via_pass ∷ Ord α ⇒ Tree α → Tree α
merge_pairs_via_pass h = pass2 (pass1 h)
