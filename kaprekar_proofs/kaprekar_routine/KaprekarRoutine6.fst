module KaprekarRoutine6

open KaprekarGapState

let sort2_desc (a b:int) = if a >= b then (a, b) else (b, a)

let sort6_desc (a b c d e f:int) =
  let (a, b) = sort2_desc a b in
  let (c, d) = sort2_desc c d in
  let (e, f) = sort2_desc e f in
  let (a, c) = sort2_desc a c in
  let (b, d) = sort2_desc b d in
  let (c, e) = sort2_desc c e in
  let (d, f) = sort2_desc d f in
  let (b, e) = sort2_desc b e in
  let (a, d) = sort2_desc a d in
  let (c, f) = sort2_desc c f in
  let (b, c) = sort2_desc b c in
  let (d, e) = sort2_desc d e in
  let (c, d) = sort2_desc c d in
  (a, b, c, d, e, f)

let kaprekar_step_digits (a b c d e f:digit) : number6 =
  let (u, v, w, x, y, z) = sort6_desc a b c d e f in
  (100000 * u + 10000 * v + 1000 * w + 100 * x + 10 * y + z) -
  (100000 * z + 10000 * y + 1000 * x + 100 * w + 10 * v + u)

let hundred_thousands (n:number6) : digit = n / 100000
let ten_thousands (n:number6) : digit = (n / 10000) % 10
let thousands (n:number6) : digit = (n / 1000) % 10
let hundreds (n:number6) : digit = (n / 100) % 10
let tens (n:number6) : digit = (n / 10) % 10
let ones (n:number6) : digit = n % 10

let kaprekar_step (n:number6) : number6 =
  kaprekar_step_digits
    (hundred_thousands n)
    (ten_thousands n)
    (thousands n)
    (hundreds n)
    (tens n)
    (ones n)

let state (outer middle inner:gap) : number6 = gap_state_6 outer middle inner

let first_step_shape (a b c d e f:digit) : Lemma
  (ensures (
    let (u, v, w, x, y, z) = sort6_desc a b c d e f in
    kaprekar_step_digits a b c d e f == state (u - z) (v - y) (w - x))) =
  let (u, v, w, x, y, z) = sort6_desc a b c d e f in
  gap_state_6_formula (u - z) (v - y) (w - x)

let repeated_digits_go_to_0 (d:digit) : Lemma
  (ensures (kaprekar_step_digits d d d d d d == 0)) =
  assert_norm (kaprekar_step_digits d d d d d d == 0)

