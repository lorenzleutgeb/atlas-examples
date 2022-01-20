(**
 * The function definitions in this file are taken from or made to match
 * Section 8 of
 *
 *   Tobias Nipkow, Hauke Brinkop
 *   Amortized Complexity Verified
 *   Journal of Automated Reasoning, Vol. 62, Iss. 3, pp. 367-391
 *   https://doi.org/10.1007/s10817-018-9459-3
 *   https://dblp.org/rec/journals/jar/NipkowB19
 *)

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
    | leaf         → (node lx x leaf)
    | node ly y ry → if x < y
      then (node (node ly y lx) x ry)
      else (node (node lx x ly) y ry)

(**
 * Original definition:
 *
 *   merge leaf h = h
 *   merge h leaf = h
 *   merge (node lx x leaf) (node ly y leaf) = link (node lx x (node ly y leaf))
 *)
merge ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α
merge h1 h2 = match h1 with
  | leaf         → h2
  | node lx x rx → match h2 with
    | leaf         → (node lx x rx)
    | node ly y ry → (~ link (node lx x (node ly y leaf)))

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
merge_isolated ∷ Ord α ⇒ Tree α ⨯ Tree α → Tree α
merge_isolated h1 h2 = match h1 with
  | leaf        → h2
  | node lx x rx → match h2 with
    | leaf        → (node lx x rx)
    | node ly y ry → if x < y
      then (node (node ly y lx) x leaf)
      else (node (node lx x ly) y leaf)

insert ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert x h = (merge (node leaf x leaf) h)

insert_isolated ∷ Ord α ⇒ α ⨯ Tree α → Tree α
insert_isolated x h = match h with
  | leaf        → (node leaf x leaf)
  | node ly y _ → if x < y
    then (node (node ly y leaf) x leaf)
    else (node (node leaf x ly) y leaf)

(* Same as `delete_min` but with `merge_pairs_isolated` instead of `pass1` and `pass2`. *)
delete_min_via_merge_pairs_isolated ∷ Ord α ⇒ Tree α → Tree α
delete_min_via_merge_pairs_isolated h = match h with
  | node l _ _ → ~ merge_pairs_isolated l

(* The same as `merge_pairs` but with `link` inlined. *)
merge_pairs_isolated ∷ Ord α ⇒ Tree α → Tree α
merge_pairs_isolated h = match h with
  | node la a ra → match ra with
    | leaf         → (node la a leaf)
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

delete_min ∷ Ord α ⇒ Tree α → Tree α
delete_min h = match h with
  | node l _ _ → ~ merge_pairs l

merge_pairs ∷ Ord α ⇒ Tree α → Tree α
merge_pairs h = match h with
  | node lx x rx → match rx with
    | leaf         → (node lx x leaf)
    | node ly y ry → (~ link (~ link (node lx x (node ly y (~ merge_pairs ry)))))

pass1 ∷ Ord α ⇒ Tree α → Tree α
pass1 h = match h with
  | node lx x rx → match rx with
    | leaf         → (node lx x leaf)
    | node ly y ry → (~ link (node lx x (node ly y (~ pass1 ry))))

pass2 ∷ Ord α ⇒ Tree α → Tree α
pass2 h = match h with
  | node l x r → (~ link (node l x (~ pass2 r)))

merge_pairs_via_pass ∷ Ord α ⇒ Tree α → Tree α
merge_pairs_via_pass h = pass2 (pass1 h)

delete_min_via_pass ∷ Ord α ⇒ Tree α → Tree α
delete_min_via_pass h = match h with
  | node l _ _ → (~ pass2 (~ pass1 l))

(**
 * Original definition:
 *
 *   is_root h = (case h of leaf → true | node l x r → r == leaf)
 *)
is_root ∷ Tree α → Bool
is_root h = match h with
  | leaf       → true
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