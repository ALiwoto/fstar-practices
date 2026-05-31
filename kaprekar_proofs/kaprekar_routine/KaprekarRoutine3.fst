module KaprekarRoutine3

type digit = d:int{0 <= d /\ d <= 9}
type number3 = n:int{0 <= n /\ n <= 999}
type delta3 = d:int{1 <= d /\ d <= 9}

let max2 (a b:int) = if a >= b then a else b
let min2 (a b:int) = if a <= b then a else b
let max3 (a b c:int) = max2 (max2 a b) c
let min3 (a b c:int) = min2 (min2 a b) c
let mid3 (a b c:int) = a + b + c - max3 a b c - min3 a b c

let kaprekar_step_digits (a b c:digit) : number3 =
  let hi = max3 a b c in
  let mid = mid3 a b c in
  let lo = min3 a b c in
  (100 * hi + 10 * mid + lo) - (100 * lo + 10 * mid + hi)

let hundreds (n:number3) : digit = n / 100
let tens (n:number3) : digit = (n / 10) % 10
let ones (n:number3) : digit = n % 10

let kaprekar_step (n:number3) : number3 = kaprekar_step_digits (hundreds n) (tens n) (ones n)
let step2 n = kaprekar_step (kaprekar_step n)
let step3 n = kaprekar_step (step2 n)
let step4 n = kaprekar_step (step3 n)
let step5 n = kaprekar_step (step4 n)

let reaches_495_from (n:number3) =
  n == 495 \/
  kaprekar_step n == 495 \/
  step2 n == 495 \/
  step3 n == 495 \/
  step4 n == 495 \/
  step5 n == 495

let delta_state (d:delta3) : number3 = 99 * d

let delta_1_reaches () : Lemma (reaches_495_from (delta_state 1)) = assert_norm (reaches_495_from (delta_state 1))
let delta_2_reaches () : Lemma (reaches_495_from (delta_state 2)) = assert_norm (reaches_495_from (delta_state 2))
let delta_3_reaches () : Lemma (reaches_495_from (delta_state 3)) = assert_norm (reaches_495_from (delta_state 3))
let delta_4_reaches () : Lemma (reaches_495_from (delta_state 4)) = assert_norm (reaches_495_from (delta_state 4))
let delta_5_reaches () : Lemma (reaches_495_from (delta_state 5)) = assert_norm (reaches_495_from (delta_state 5))
let delta_6_reaches () : Lemma (reaches_495_from (delta_state 6)) = assert_norm (reaches_495_from (delta_state 6))
let delta_7_reaches () : Lemma (reaches_495_from (delta_state 7)) = assert_norm (reaches_495_from (delta_state 7))
let delta_8_reaches () : Lemma (reaches_495_from (delta_state 8)) = assert_norm (reaches_495_from (delta_state 8))
let delta_9_reaches () : Lemma (reaches_495_from (delta_state 9)) = assert_norm (reaches_495_from (delta_state 9))

let delta_reaches_495 (d:delta3) : Lemma (reaches_495_from (delta_state d)) =
  if d == 1 then (assert (delta_state d == delta_state 1); delta_1_reaches ()) else
  if d == 2 then (assert (delta_state d == delta_state 2); delta_2_reaches ()) else
  if d == 3 then (assert (delta_state d == delta_state 3); delta_3_reaches ()) else
  if d == 4 then (assert (delta_state d == delta_state 4); delta_4_reaches ()) else
  if d == 5 then (assert (delta_state d == delta_state 5); delta_5_reaches ()) else
  if d == 6 then (assert (delta_state d == delta_state 6); delta_6_reaches ()) else
  if d == 7 then (assert (delta_state d == delta_state 7); delta_7_reaches ()) else
  if d == 8 then (assert (delta_state d == delta_state 8); delta_8_reaches ()) else
  (assert (delta_state d == delta_state 9); delta_9_reaches ())

let distinct_digits (a b c:digit) = a <> b \/ b <> c

let first_step_delta (a b c:digit) : Lemma
  (requires (distinct_digits a b c))
  (ensures (kaprekar_step_digits a b c == delta_state (max3 a b c - min3 a b c))) =
  ()

let reaches_495 (a b c:digit) : Lemma
  (requires (distinct_digits a b c))
  (ensures (reaches_495_from (kaprekar_step_digits a b c))) =
  first_step_delta a b c;
  delta_reaches_495 (max3 a b c - min3 a b c)

let repeated_digits_go_to_0 (d:digit) : Lemma
  (ensures (kaprekar_step_digits d d d == 0)) =
  assert_norm (kaprekar_step_digits d d d == 0)

let fixed_point_495 () : Lemma
  (ensures (kaprekar_step 495 == 495)) =
  assert_norm (kaprekar_step 495 == 495)