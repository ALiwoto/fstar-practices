module KaprekarRoutine5

open KaprekarGapState

let sort2_desc (a b:int) = if a >= b then (a, b) else (b, a)

let sort5_desc (a b c d e:int) =
  let (a, b) = sort2_desc a b in
  let (d, e) = sort2_desc d e in
  let (c, e) = sort2_desc c e in
  let (c, d) = sort2_desc c d in
  let (b, e) = sort2_desc b e in
  let (a, d) = sort2_desc a d in
  let (a, c) = sort2_desc a c in
  let (b, d) = sort2_desc b d in
  let (b, c) = sort2_desc b c in
  (a, b, c, d, e)

let kaprekar_step_digits (a b c d e:digit) : number5 =
  let (v, w, x, y, z) = sort5_desc a b c d e in
  (10000 * v + 1000 * w + 100 * x + 10 * y + z) -
  (10000 * z + 1000 * y + 100 * x + 10 * w + v)

let ten_thousands (n:number5) : digit = n / 10000
let thousands (n:number5) : digit = (n / 1000) % 10
let hundreds (n:number5) : digit = (n / 100) % 10
let tens (n:number5) : digit = (n / 10) % 10
let ones (n:number5) : digit = n % 10

let kaprekar_step (n:number5) : number5 =
  kaprekar_step_digits (ten_thousands n) (thousands n) (hundreds n) (tens n) (ones n)

let state (outer inner:gap) : number5 = gap_state_5 outer inner

let first_step_shape (a b c d e:digit) : Lemma
  (ensures (
    let (v, w, x, y, z) = sort5_desc a b c d e in
    kaprekar_step_digits a b c d e == state (v - z) (w - y))) =
  let (v, w, x, y, z) = sort5_desc a b c d e in
  gap_state_5_formula (v - z) (w - y)

let repeated_digits_go_to_0 (d:digit) : Lemma
  (ensures (kaprekar_step_digits d d d d d == 0)) =
  assert_norm (kaprekar_step_digits d d d d d == 0)

