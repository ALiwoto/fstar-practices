module KaprekarRoutine2

type digit = d:int{0 <= d /\ d <= 9}
type number2 = n:int{0 <= n /\ n <= 99}
type delta2 = d:int{1 <= d /\ d <= 9}

let max2 (a b:int) = if a >= b then a else b
let min2 (a b:int) = if a <= b then a else b

let kaprekar_step_digits (a b:digit) : number2 =
  let hi = max2 a b in
  let lo = min2 a b in
  (10 * hi + lo) - (10 * lo + hi)

let tens (n:number2) : digit = n / 10
let ones (n:number2) : digit = n % 10

let kaprekar_step (n:number2) : number2 = kaprekar_step_digits (tens n) (ones n)
let step2 n = kaprekar_step (kaprekar_step n)
let step3 n = kaprekar_step (step2 n)
let step4 n = kaprekar_step (step3 n)
let step5 n = kaprekar_step (step4 n)

let reaches_09_from (n:number2) =
  n == 9 \/
  kaprekar_step n == 9 \/
  step2 n == 9 \/
  step3 n == 9 \/
  step4 n == 9 \/
  step5 n == 9

let delta_state (d:delta2) : number2 = 9 * d

let delta_1_reaches () : Lemma (reaches_09_from (delta_state 1)) = assert_norm (reaches_09_from (delta_state 1))
let delta_2_reaches () : Lemma (reaches_09_from (delta_state 2)) = assert_norm (reaches_09_from (delta_state 2))
let delta_3_reaches () : Lemma (reaches_09_from (delta_state 3)) = assert_norm (reaches_09_from (delta_state 3))
let delta_4_reaches () : Lemma (reaches_09_from (delta_state 4)) = assert_norm (reaches_09_from (delta_state 4))
let delta_5_reaches () : Lemma (reaches_09_from (delta_state 5)) = assert_norm (reaches_09_from (delta_state 5))
let delta_6_reaches () : Lemma (reaches_09_from (delta_state 6)) = assert_norm (reaches_09_from (delta_state 6))
let delta_7_reaches () : Lemma (reaches_09_from (delta_state 7)) = assert_norm (reaches_09_from (delta_state 7))
let delta_8_reaches () : Lemma (reaches_09_from (delta_state 8)) = assert_norm (reaches_09_from (delta_state 8))
let delta_9_reaches () : Lemma (reaches_09_from (delta_state 9)) = assert_norm (reaches_09_from (delta_state 9))

let delta_reaches_09 (d:delta2) : Lemma (reaches_09_from (delta_state d)) =
  if d == 1 then (assert (delta_state d == delta_state 1); delta_1_reaches ()) else
  if d == 2 then (assert (delta_state d == delta_state 2); delta_2_reaches ()) else
  if d == 3 then (assert (delta_state d == delta_state 3); delta_3_reaches ()) else
  if d == 4 then (assert (delta_state d == delta_state 4); delta_4_reaches ()) else
  if d == 5 then (assert (delta_state d == delta_state 5); delta_5_reaches ()) else
  if d == 6 then (assert (delta_state d == delta_state 6); delta_6_reaches ()) else
  if d == 7 then (assert (delta_state d == delta_state 7); delta_7_reaches ()) else
  if d == 8 then (assert (delta_state d == delta_state 8); delta_8_reaches ()) else
  (assert (delta_state d == delta_state 9); delta_9_reaches ())

let distinct_digits (a b:digit) = a <> b

let first_step_delta (a b:digit) : Lemma
  (requires (distinct_digits a b))
  (ensures (kaprekar_step_digits a b == delta_state (max2 a b - min2 a b))) =
  ()

let reaches_09 (a b:digit) : Lemma
  (requires (distinct_digits a b))
  (ensures (reaches_09_from (kaprekar_step_digits a b))) =
  first_step_delta a b;
  delta_reaches_09 (max2 a b - min2 a b)

let repeated_digits_go_to_0 (d:digit) : Lemma
  (ensures (kaprekar_step_digits d d == 0)) =
  assert_norm (kaprekar_step_digits d d == 0)

let nine_is_in_the_cycle () : Lemma
  (ensures (step5 9 == 9)) =
  assert_norm (step5 9 == 9)