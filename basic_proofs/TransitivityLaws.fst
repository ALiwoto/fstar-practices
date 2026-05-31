module TransitivityLaws

let transitive_implication (p q r : prop) : Lemma
  (requires (p ==> q) /\ (q ==> r))
  (ensures (p ==> r))
  = ()
