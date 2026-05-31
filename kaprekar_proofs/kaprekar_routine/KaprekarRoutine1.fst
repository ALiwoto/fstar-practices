module KaprekarRoutine1

type digit = d:int{0 <= d /\ d <= 9}

type number1 = n:int{0 <= n /\ n <= 9}

let kaprekar_step_digit (d:digit) : number1 = d - d

let kaprekar_step (n:number1) : number1 = kaprekar_step_digit n

let reaches_0 (d:digit) : Lemma
  (ensures (kaprekar_step_digit d == 0)) =
  ()

let fixed_point_0 () : Lemma
  (ensures (kaprekar_step 0 == 0)) =
  assert_norm (kaprekar_step 0 == 0)