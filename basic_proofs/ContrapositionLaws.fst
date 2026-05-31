module ContrapositionLaws

// Let P and Q be two propositions.
// (P ⟹ Q) ⟺ (¬Q ⟹ ¬P)

let contraposition (p: Type0) (q: Type0) : Lemma 
  (ensures (p ==> q) <==> (~q ==> ~p)) = 
  ()
