(**
 * f depends on g
 * e depends on h
 * g and h are mutually recursive, part of the same SCC
 * h additionally depends on i
 *
 *  e ->  h -> i
 *       ||
 *  f -> g -> j
 *
 *  Correct ordering:
 *    1.a. i
 *    1.b. j
 *    2. h and g
 *    3.a. e
 *    3.b. f
 *  (a/b are interchangable)
 *)

f x = (f (g x))

e x = (h x)

g x = (h (j x))

h x = (g (i x))

i x = x

j x = x