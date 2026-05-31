module AbsorptionLaws

// Lemma for the first Absorption Law: p \/ (p /\ q) <==> p

val absorption_law_1 (p q: Type0) : Lemma ((p \/ (p /\ q)) <==> p)

let absorption_law_1 p q = () // Proof is automatic for this basic tautology


// in mathematics, we often write a chain of equalities or equivalences like 
// A=B=C=D to mean (A=B)∧(B=C)∧(C=D). This is a very convenient shorthand.
// However, in F-star's type system, 
// a Lemma (Prop) statement is a claim that the single proposition Prop is true.
// The <==> operator is a binary logical operator that takes two propositions on 
// its left and right sides and forms a new proposition which is true if and only if
// both sides have the same truth value.
let absorption_law1_intermediate (p q r: Type0) = ((p \/ p) /\ (p \/ q) /\ (p \/ r))

val absorption_law1_v2 (p q r: Type0)
    : Lemma
    (((p \/ (p /\ q /\ r)) <==> absorption_law1_intermediate p q r) /\
      (absorption_law1_intermediate p q r <==> p))

let absorption_law1_v2 p q r = ()

// Lemma for the second Absorption Law: p /\ (p \/ q) <==> p

val absorption_law_2 (p q: Type0) : Lemma ((p /\ (p \/ q)) <==> p)

let absorption_law_2 p q = () // Proof is automatic for this basic tautology


