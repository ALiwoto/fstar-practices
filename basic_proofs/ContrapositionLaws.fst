module ContrapositionLaws

// Let P and Q be two propositions.
// (P ⟹ Q) ⟺ (¬Q ⟹ ¬P)

let contraposition (p: prop) (q: prop) : Lemma 
  (ensures (p ==> q) <==> (~q ==> ~p)) = 
  ()
