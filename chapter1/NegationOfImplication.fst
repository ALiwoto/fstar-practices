module NegationOfImplication

// The negation of an implication: 
// "If P, then Q" (represented as P → Q) is "P and not Q" (represented as P ∧ ¬Q).
// In other words, to negate an implication, you need to find a case where the antecedent (P) is true,
// but the consequent (Q) is false.
// See also: https://math.stackexchange.com/q/2417770

let negation_of_implication (p: Type0) (q: Type0) : Lemma
  (ensures (~(p ==> q)) <==> (p /\ ~q)) =
  ()

// ∀x,y : xy=0 → x=0 ∨ y=0
// This is a logical statement saying "for all x and y, if xy=0, then either x=0 or y=0".
// This is a property that holds in integral domains.
let existence_zero_product (x y : int) : Lemma
  (requires (op_Multiply x y = 0))
  (ensures (x = 0 || y = 0)) = ()

// NOT-∃ x,y : xy=0 ∧ (x≠0 ∧ y≠0)
// "for all x and y, xy=0 and (x is not 0 and y is not 0)"
let non_existence_zero_product (x y : int) : Lemma
  (requires (op_Multiply x y = 0 && x <> 0 && y <> 0))
  (ensures (false)) = ()
