#! /usr/bin/env nix-shell
#! nix-shell -i bash -p calc coreutils

# NOTE: To run this script without having nix-shell installed,
# change the shebang to
#
#   #! /usr/bin/env bash
#
# but make sure to have `calc` <http://www.isthe.com/chongo/tech/comp/calc/>
# in $PATH.

# This script generates the input programs for Table 2 in the CAV 2022 paper.
# The annotations below were added to enable typechecking.

N="1/3 1/2 2/3"

RESULTS=(
# P = 1/3
"2/3" "1"
"3/4" "9/8"
"5/6" "5/4"

# P = 1/2
"5/6" "5/6"
"1" "1"
"7/6" "7/6"

# P = 2/3
"7/9" "77/54"
"5/6" "55/36"
"8/9" "44/27"
)

function inverse {
	calc "config(\"mode\",\"fraction\"); print(1 - $1);" | tail -n 1 | tr -d "[[:space:]]"
}

function half {
	calc "config(\"mode\",\"fraction\"); print($1 / 2);" | tail -n 1 | tr -d "[[:space:]]"
}

function shape {
	RANK=$1
	LOG=$2
	C=$3
	RANK_BY_2=$(half $RANK)
	echo "[[0 ↦ $RANK, (1 0) ↦ $LOG, (0 2) ↦ $C] → [0 ↦ $RANK, (0 2) ↦ $C], {[(1 0) ↦ $RANK_BY_2] → [(1 0) ↦ $RANK_BY_2]}]"
}

I=0

for P in $N
do
	for C_REC in $N
	do
		C_ROT=$(inverse $C_REC)
		F=P${P//\//}C${C_REC//\//}.ml
		A=$(shape ${RESULTS[$I]} ${RESULTS[$(expr $I + 1)]} ${C_REC})
		I=$(expr $I + 2)
		echo "P = ${P}    C_REC = ${C_REC}    C_ROT = ${C_ROT}"
		echo "$A"
		echo "-> $F"
		echo ""
		cat > $F << EOT
(**
 * This file was automatically generated by 'generate.sh'.
 *
 * DO NOT EDIT
 *
 * Cost for recursion : $P = 1 - $C_ROT
 * Cost for rotation  : $C_ROT = 1 - $C_REC
 * Coin probability   : $P
 *)

splay ∷ Ord α ⇒ (α ⨯ Tree α) → Tree α | $A
splay a t = match t with
  | node cl c cr → if a == c
    then (node cl c cr)
    else if a < c
      then match cl with
        | leaf        → (node leaf c cr)
        | node bl b br → if a == b
          then (node (node bl a br) c cr)  (* No rotation! *)
          else if a < b
            then match bl with
              | leaf → (node leaf b (node br c cr))
              | bl   → match ~ $C_REC splay a bl with
                | node al a1 ar → if coin $P
                  then ~ $C_ROT (node al a1 (node ar b (node br c cr)))
                  else (node (node (node al a1 ar) b br) c cr)
            else match br with
              | leaf → (node bl b (node leaf c cr))
              | br   → match ~ $C_REC splay a br with
                | node al a1 ar → if coin $P
                  then ~ $C_ROT (node (node bl b al) a1 (node ar c cr))
                  else (node (node bl b (node al a1 ar)) c cr)
      else match cr with
        | leaf         → (node cl c leaf)
        | node bl b br → if a == b
          then (node cl c (node bl a br))  (* No rotation! *)
          else if a < b
            then match bl with
              | leaf → (node (node cl c leaf) b br)
              | bl   → match ~ $C_REC splay a bl with
                | node al a1 ar → if coin $P
                  then ~ $C_ROT (node (node cl c al) a1 (node ar b br))
                  else (node cl c (node (node al a1 ar) b br))
            else match br with
              | leaf → (node (node cl c bl) b leaf)
              | br   → match ~ $C_REC splay a br with
                | node al a1 ar → if coin $P
                  then ~ $C_ROT (node (node (node cl c bl) b al) a1 ar)
                  else (node cl c (node bl b (node al a1 ar)))

splay_zigzig ∷ (α ⨯ Tree α) → Tree α | $A
splay_zigzig a t = match t with
  | node cl c cr → match cl with  (* assume a < c *)
    | leaf         → (node leaf c cr)
    | node bl b br → match bl with  (* assume a < b *)
      | leaf → (node leaf b (node br c cr))
      | bl   → match ~ $C_REC splay_zigzig a bl with
        | node al a1 ar → if coin $P
          then ~ $C_ROT (node al a1 (node ar b (node br c cr)))
          else (node (node (node al a1 ar) b br) c cr)

EOT
	done
done

