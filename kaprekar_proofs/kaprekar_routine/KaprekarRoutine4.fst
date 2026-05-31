module KaprekarRoutine4

type digit = d:int{0 <= d /\ d <= 9}
type number4 = n:int{0 <= n /\ n <= 9999}
type alpha4 = a:int{1 <= a /\ a <= 9}

let sort2_desc (a b:int) = if a >= b then (a, b) else (b, a)
let sort4_desc (a b c d:int) =
  let (x0, x1) = sort2_desc a b in
  let (x2, x3) = sort2_desc c d in
  let (y0, y2) = sort2_desc x0 x2 in
  let (y1, y3) = sort2_desc x1 x3 in
  let (z1, z2) = sort2_desc y1 y2 in
  (y0, z1, z2, y3)
let kaprekar_step_digits (a b c d:digit) : number4 =
  let (w, x, y, z) = sort4_desc a b c d in
  (1000 * w + 100 * x + 10 * y + z) - (1000 * z + 100 * y + 10 * x + w)
let thousands (n:number4) : digit = n / 1000
let hundreds (n:number4) : digit = (n / 100) % 10
let tens (n:number4) : digit = (n / 10) % 10
let ones (n:number4) : digit = n % 10
let kaprekar_step (n:number4) : number4 = kaprekar_step_digits (thousands n) (hundreds n) (tens n) (ones n)
let step2 n = kaprekar_step (kaprekar_step n)
let step3 n = kaprekar_step (step2 n)
let step4 n = kaprekar_step (step3 n)
let step5 n = kaprekar_step (step4 n)
let step6 n = kaprekar_step (step5 n)
let state (a:alpha4) (b:int{0 <= b /\ b <= a}) : number4 = 999 * a + 90 * b
let reaches_6174_from (n:number4) =
  n == 6174 \/
  kaprekar_step n == 6174 \/
  step2 n == 6174 \/
  step3 n == 6174 \/
  step4 n == 6174 \/
  step5 n == 6174 \/
  step6 n == 6174
let state_1_0_reaches () : Lemma (reaches_6174_from (state 1 0)) = assert_norm (reaches_6174_from (state 1 0))
let state_1_1_reaches () : Lemma (reaches_6174_from (state 1 1)) = assert_norm (reaches_6174_from (state 1 1))
let state_2_0_reaches () : Lemma (reaches_6174_from (state 2 0)) = assert_norm (reaches_6174_from (state 2 0))
let state_2_1_reaches () : Lemma (reaches_6174_from (state 2 1)) = assert_norm (reaches_6174_from (state 2 1))
let state_2_2_reaches () : Lemma (reaches_6174_from (state 2 2)) = assert_norm (reaches_6174_from (state 2 2))
let state_3_0_reaches () : Lemma (reaches_6174_from (state 3 0)) = assert_norm (reaches_6174_from (state 3 0))
let state_3_1_reaches () : Lemma (reaches_6174_from (state 3 1)) = assert_norm (reaches_6174_from (state 3 1))
let state_3_2_reaches () : Lemma (reaches_6174_from (state 3 2)) = assert_norm (reaches_6174_from (state 3 2))
let state_3_3_reaches () : Lemma (reaches_6174_from (state 3 3)) = assert_norm (reaches_6174_from (state 3 3))
let state_4_0_reaches () : Lemma (reaches_6174_from (state 4 0)) = assert_norm (reaches_6174_from (state 4 0))
let state_4_1_reaches () : Lemma (reaches_6174_from (state 4 1)) = assert_norm (reaches_6174_from (state 4 1))
let state_4_2_reaches () : Lemma (reaches_6174_from (state 4 2)) = assert_norm (reaches_6174_from (state 4 2))
let state_4_3_reaches () : Lemma (reaches_6174_from (state 4 3)) = assert_norm (reaches_6174_from (state 4 3))
let state_4_4_reaches () : Lemma (reaches_6174_from (state 4 4)) = assert_norm (reaches_6174_from (state 4 4))
let state_5_0_reaches () : Lemma (reaches_6174_from (state 5 0)) = assert_norm (reaches_6174_from (state 5 0))
let state_5_1_reaches () : Lemma (reaches_6174_from (state 5 1)) = assert_norm (reaches_6174_from (state 5 1))
let state_5_2_reaches () : Lemma (reaches_6174_from (state 5 2)) = assert_norm (reaches_6174_from (state 5 2))
let state_5_3_reaches () : Lemma (reaches_6174_from (state 5 3)) = assert_norm (reaches_6174_from (state 5 3))
let state_5_4_reaches () : Lemma (reaches_6174_from (state 5 4)) = assert_norm (reaches_6174_from (state 5 4))
let state_5_5_reaches () : Lemma (reaches_6174_from (state 5 5)) = assert_norm (reaches_6174_from (state 5 5))
let state_6_0_reaches () : Lemma (reaches_6174_from (state 6 0)) = assert_norm (reaches_6174_from (state 6 0))
let state_6_1_reaches () : Lemma (reaches_6174_from (state 6 1)) = assert_norm (reaches_6174_from (state 6 1))
let state_6_2_reaches () : Lemma (reaches_6174_from (state 6 2)) = assert_norm (reaches_6174_from (state 6 2))
let state_6_3_reaches () : Lemma (reaches_6174_from (state 6 3)) = assert_norm (reaches_6174_from (state 6 3))
let state_6_4_reaches () : Lemma (reaches_6174_from (state 6 4)) = assert_norm (reaches_6174_from (state 6 4))
let state_6_5_reaches () : Lemma (reaches_6174_from (state 6 5)) = assert_norm (reaches_6174_from (state 6 5))
let state_6_6_reaches () : Lemma (reaches_6174_from (state 6 6)) = assert_norm (reaches_6174_from (state 6 6))
let state_7_0_reaches () : Lemma (reaches_6174_from (state 7 0)) = assert_norm (reaches_6174_from (state 7 0))
let state_7_1_reaches () : Lemma (reaches_6174_from (state 7 1)) = assert_norm (reaches_6174_from (state 7 1))
let state_7_2_reaches () : Lemma (reaches_6174_from (state 7 2)) = assert_norm (reaches_6174_from (state 7 2))
let state_7_3_reaches () : Lemma (reaches_6174_from (state 7 3)) = assert_norm (reaches_6174_from (state 7 3))
let state_7_4_reaches () : Lemma (reaches_6174_from (state 7 4)) = assert_norm (reaches_6174_from (state 7 4))
let state_7_5_reaches () : Lemma (reaches_6174_from (state 7 5)) = assert_norm (reaches_6174_from (state 7 5))
let state_7_6_reaches () : Lemma (reaches_6174_from (state 7 6)) = assert_norm (reaches_6174_from (state 7 6))
let state_7_7_reaches () : Lemma (reaches_6174_from (state 7 7)) = assert_norm (reaches_6174_from (state 7 7))
let state_8_0_reaches () : Lemma (reaches_6174_from (state 8 0)) = assert_norm (reaches_6174_from (state 8 0))
let state_8_1_reaches () : Lemma (reaches_6174_from (state 8 1)) = assert_norm (reaches_6174_from (state 8 1))
let state_8_2_reaches () : Lemma (reaches_6174_from (state 8 2)) = assert_norm (reaches_6174_from (state 8 2))
let state_8_3_reaches () : Lemma (reaches_6174_from (state 8 3)) = assert_norm (reaches_6174_from (state 8 3))
let state_8_4_reaches () : Lemma (reaches_6174_from (state 8 4)) = assert_norm (reaches_6174_from (state 8 4))
let state_8_5_reaches () : Lemma (reaches_6174_from (state 8 5)) = assert_norm (reaches_6174_from (state 8 5))
let state_8_6_reaches () : Lemma (reaches_6174_from (state 8 6)) = assert_norm (reaches_6174_from (state 8 6))
let state_8_7_reaches () : Lemma (reaches_6174_from (state 8 7)) = assert_norm (reaches_6174_from (state 8 7))
let state_8_8_reaches () : Lemma (reaches_6174_from (state 8 8)) = assert_norm (reaches_6174_from (state 8 8))
let state_9_0_reaches () : Lemma (reaches_6174_from (state 9 0)) = assert_norm (reaches_6174_from (state 9 0))
let state_9_1_reaches () : Lemma (reaches_6174_from (state 9 1)) = assert_norm (reaches_6174_from (state 9 1))
let state_9_2_reaches () : Lemma (reaches_6174_from (state 9 2)) = assert_norm (reaches_6174_from (state 9 2))
let state_9_3_reaches () : Lemma (reaches_6174_from (state 9 3)) = assert_norm (reaches_6174_from (state 9 3))
let state_9_4_reaches () : Lemma (reaches_6174_from (state 9 4)) = assert_norm (reaches_6174_from (state 9 4))
let state_9_5_reaches () : Lemma (reaches_6174_from (state 9 5)) = assert_norm (reaches_6174_from (state 9 5))
let state_9_6_reaches () : Lemma (reaches_6174_from (state 9 6)) = assert_norm (reaches_6174_from (state 9 6))
let state_9_7_reaches () : Lemma (reaches_6174_from (state 9 7)) = assert_norm (reaches_6174_from (state 9 7))
let state_9_8_reaches () : Lemma (reaches_6174_from (state 9 8)) = assert_norm (reaches_6174_from (state 9 8))
let state_9_9_reaches () : Lemma (reaches_6174_from (state 9 9)) = assert_norm (reaches_6174_from (state 9 9))
let state_reaches_alpha_1 (b:int{0 <= b /\ b <= 1}) : Lemma (reaches_6174_from (state 1 b)) =
  if b == 0 then (assert (state 1 b == state 1 0); state_1_0_reaches ()) else
  (assert (state 1 b == state 1 1); state_1_1_reaches ())
let state_reaches_alpha_2 (b:int{0 <= b /\ b <= 2}) : Lemma (reaches_6174_from (state 2 b)) =
  if b == 0 then (assert (state 2 b == state 2 0); state_2_0_reaches ()) else
  if b == 1 then (assert (state 2 b == state 2 1); state_2_1_reaches ()) else
  (assert (state 2 b == state 2 2); state_2_2_reaches ())
let state_reaches_alpha_3 (b:int{0 <= b /\ b <= 3}) : Lemma (reaches_6174_from (state 3 b)) =
  if b == 0 then (assert (state 3 b == state 3 0); state_3_0_reaches ()) else
  if b == 1 then (assert (state 3 b == state 3 1); state_3_1_reaches ()) else
  if b == 2 then (assert (state 3 b == state 3 2); state_3_2_reaches ()) else
  (assert (state 3 b == state 3 3); state_3_3_reaches ())
let state_reaches_alpha_4 (b:int{0 <= b /\ b <= 4}) : Lemma (reaches_6174_from (state 4 b)) =
  if b == 0 then (assert (state 4 b == state 4 0); state_4_0_reaches ()) else
  if b == 1 then (assert (state 4 b == state 4 1); state_4_1_reaches ()) else
  if b == 2 then (assert (state 4 b == state 4 2); state_4_2_reaches ()) else
  if b == 3 then (assert (state 4 b == state 4 3); state_4_3_reaches ()) else
  (assert (state 4 b == state 4 4); state_4_4_reaches ())
let state_reaches_alpha_5 (b:int{0 <= b /\ b <= 5}) : Lemma (reaches_6174_from (state 5 b)) =
  if b == 0 then (assert (state 5 b == state 5 0); state_5_0_reaches ()) else
  if b == 1 then (assert (state 5 b == state 5 1); state_5_1_reaches ()) else
  if b == 2 then (assert (state 5 b == state 5 2); state_5_2_reaches ()) else
  if b == 3 then (assert (state 5 b == state 5 3); state_5_3_reaches ()) else
  if b == 4 then (assert (state 5 b == state 5 4); state_5_4_reaches ()) else
  (assert (state 5 b == state 5 5); state_5_5_reaches ())
let state_reaches_alpha_6 (b:int{0 <= b /\ b <= 6}) : Lemma (reaches_6174_from (state 6 b)) =
  if b == 0 then (assert (state 6 b == state 6 0); state_6_0_reaches ()) else
  if b == 1 then (assert (state 6 b == state 6 1); state_6_1_reaches ()) else
  if b == 2 then (assert (state 6 b == state 6 2); state_6_2_reaches ()) else
  if b == 3 then (assert (state 6 b == state 6 3); state_6_3_reaches ()) else
  if b == 4 then (assert (state 6 b == state 6 4); state_6_4_reaches ()) else
  if b == 5 then (assert (state 6 b == state 6 5); state_6_5_reaches ()) else
  (assert (state 6 b == state 6 6); state_6_6_reaches ())
let state_reaches_alpha_7 (b:int{0 <= b /\ b <= 7}) : Lemma (reaches_6174_from (state 7 b)) =
  if b == 0 then (assert (state 7 b == state 7 0); state_7_0_reaches ()) else
  if b == 1 then (assert (state 7 b == state 7 1); state_7_1_reaches ()) else
  if b == 2 then (assert (state 7 b == state 7 2); state_7_2_reaches ()) else
  if b == 3 then (assert (state 7 b == state 7 3); state_7_3_reaches ()) else
  if b == 4 then (assert (state 7 b == state 7 4); state_7_4_reaches ()) else
  if b == 5 then (assert (state 7 b == state 7 5); state_7_5_reaches ()) else
  if b == 6 then (assert (state 7 b == state 7 6); state_7_6_reaches ()) else
  (assert (state 7 b == state 7 7); state_7_7_reaches ())
let state_reaches_alpha_8 (b:int{0 <= b /\ b <= 8}) : Lemma (reaches_6174_from (state 8 b)) =
  if b == 0 then (assert (state 8 b == state 8 0); state_8_0_reaches ()) else
  if b == 1 then (assert (state 8 b == state 8 1); state_8_1_reaches ()) else
  if b == 2 then (assert (state 8 b == state 8 2); state_8_2_reaches ()) else
  if b == 3 then (assert (state 8 b == state 8 3); state_8_3_reaches ()) else
  if b == 4 then (assert (state 8 b == state 8 4); state_8_4_reaches ()) else
  if b == 5 then (assert (state 8 b == state 8 5); state_8_5_reaches ()) else
  if b == 6 then (assert (state 8 b == state 8 6); state_8_6_reaches ()) else
  if b == 7 then (assert (state 8 b == state 8 7); state_8_7_reaches ()) else
  (assert (state 8 b == state 8 8); state_8_8_reaches ())
let state_reaches_alpha_9 (b:int{0 <= b /\ b <= 9}) : Lemma (reaches_6174_from (state 9 b)) =
  if b == 0 then (assert (state 9 b == state 9 0); state_9_0_reaches ()) else
  if b == 1 then (assert (state 9 b == state 9 1); state_9_1_reaches ()) else
  if b == 2 then (assert (state 9 b == state 9 2); state_9_2_reaches ()) else
  if b == 3 then (assert (state 9 b == state 9 3); state_9_3_reaches ()) else
  if b == 4 then (assert (state 9 b == state 9 4); state_9_4_reaches ()) else
  if b == 5 then (assert (state 9 b == state 9 5); state_9_5_reaches ()) else
  if b == 6 then (assert (state 9 b == state 9 6); state_9_6_reaches ()) else
  if b == 7 then (assert (state 9 b == state 9 7); state_9_7_reaches ()) else
  if b == 8 then (assert (state 9 b == state 9 8); state_9_8_reaches ()) else
  (assert (state 9 b == state 9 9); state_9_9_reaches ())
let state_reaches_6174 (a:alpha4) (b:int{0 <= b /\ b <= a}) : Lemma (reaches_6174_from (state a b)) =
  if a == 1 then (assert (state a b == state 1 b); state_reaches_alpha_1 b) else
  if a == 2 then (assert (state a b == state 2 b); state_reaches_alpha_2 b) else
  if a == 3 then (assert (state a b == state 3 b); state_reaches_alpha_3 b) else
  if a == 4 then (assert (state a b == state 4 b); state_reaches_alpha_4 b) else
  if a == 5 then (assert (state a b == state 5 b); state_reaches_alpha_5 b) else
  if a == 6 then (assert (state a b == state 6 b); state_reaches_alpha_6 b) else
  if a == 7 then (assert (state a b == state 7 b); state_reaches_alpha_7 b) else
  if a == 8 then (assert (state a b == state 8 b); state_reaches_alpha_8 b) else
  (assert (state a b == state 9 b); state_reaches_alpha_9 b)

let fixed_point_6174 () : Lemma (kaprekar_step 6174 == 6174) = assert_norm (kaprekar_step 6174 == 6174)

let distinct_digits (a b c d:digit) = a <> b \/ b <> c \/ c <> d

let repeated_digits_go_to_0 (d:digit) : Lemma
  (ensures (kaprekar_step_digits d d d d == 0)) =
  assert_norm (kaprekar_step_digits d d d d == 0)

let first_step_shape (a b c d:digit) : Lemma
  (requires (distinct_digits a b c d))
  (ensures (
    let (w, x, y, z) = sort4_desc a b c d in
    kaprekar_step_digits a b c d == state (w - z) (x - y))) =
  ()

let reaches_6174 (a b c d:digit) : Lemma
  (requires (distinct_digits a b c d))
  (ensures (reaches_6174_from (kaprekar_step_digits a b c d))) =
  let (w, x, y, z) = sort4_desc a b c d in
  first_step_shape a b c d;
  state_reaches_6174 (w - z) (x - y)
