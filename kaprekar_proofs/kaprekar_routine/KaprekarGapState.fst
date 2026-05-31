module KaprekarGapState

type digit = d:int{0 <= d /\ d <= 9}
type gap = g:int{0 <= g /\ g <= 9}
type nonzero_gap = g:int{1 <= g /\ g <= 9}

type number1 = n:int{0 <= n /\ n <= 9}
type number2 = n:int{0 <= n /\ n <= 99}
type number3 = n:int{0 <= n /\ n <= 999}
type number4 = n:int{0 <= n /\ n <= 9999}
type number5 = n:int{0 <= n /\ n <= 99999}
type number6 = n:int{0 <= n /\ n <= 999999}

let rec pow10 (n:nat) : Tot int (decreases n) =
  match n with
  | 0 -> 1
  | _ -> 10 * pow10 (n - 1)

let coefficient (width:nat{width > 0}) (position:nat{2 * position < width}) : int =
  pow10 (width - 1 - position) - pow10 position

let gap_state_1 : number1 = 0
let gap_state_2 (outer:gap) : number2 = coefficient 2 0 * outer
let gap_state_3 (outer:gap) : number3 = coefficient 3 0 * outer
let gap_state_4 (outer:gap) (inner:gap) : number4 =
  coefficient 4 0 * outer + coefficient 4 1 * inner
let gap_state_5 (outer:gap) (inner:gap) : number5 =
  coefficient 5 0 * outer + coefficient 5 1 * inner
let gap_state_6 (outer:gap) (middle:gap) (inner:gap) : number6 =
  coefficient 6 0 * outer + coefficient 6 1 * middle + coefficient 6 2 * inner

let gap_state_2_formula (outer:gap)
  : Lemma (gap_state_2 outer == 9 * outer) =
  assert_norm (coefficient 2 0 == 9)

let gap_state_3_formula (outer:gap)
  : Lemma (gap_state_3 outer == 99 * outer) =
  assert_norm (coefficient 3 0 == 99)

let gap_state_4_formula (outer inner:gap)
  : Lemma (gap_state_4 outer inner == 999 * outer + 90 * inner) =
  assert_norm (coefficient 4 0 == 999 /\ coefficient 4 1 == 90)

let gap_state_5_formula (outer inner:gap)
  : Lemma (gap_state_5 outer inner == 9999 * outer + 990 * inner) =
  assert_norm (coefficient 5 0 == 9999 /\ coefficient 5 1 == 990)

let gap_state_6_formula (outer middle inner:gap)
  : Lemma (gap_state_6 outer middle inner == 99999 * outer + 9990 * middle + 900 * inner) =
  assert_norm (coefficient 6 0 == 99999 /\ coefficient 6 1 == 9990 /\ coefficient 6 2 == 900)
