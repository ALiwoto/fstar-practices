module TransitivityLaws

let transitive_implication (p q r : Type0) : Lemma
  (requires (p ==> q) /\ (q ==> r))
  (ensures (p ==> r))
  = ()
