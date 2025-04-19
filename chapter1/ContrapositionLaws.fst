module ContrapositionLaws


let contraposition (p:Type0) (q:Type0) : Lemma 
  (ensures (p ==> q) <==> (~q ==> ~p)) = 
  ()
