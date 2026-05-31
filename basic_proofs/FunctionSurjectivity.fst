module FunctionSurjectivity

// open FStar.Math.Lemmas

(* Define even integers *)
type even_int = n:int{n % 2 == 0}

(* Our function: double any integer *)
let double (x:int) : even_int = (op_Multiply 2 x)

(* Witness function: for any even integer, find a pre-image *)
let half (e:even_int) : int = (e / 2)

(* Custom lemma: For even integers e, 2 * (e / 2) = e *)
let lemma_double_half_even (e:even_int) : Lemma (ensures (op_Multiply 2 (e / 2)) == e) =
  // For even integers e, e % 2 = 0
  // By Euclidean division: e = (e / 2) * 2 + (e % 2)
  // Since e % 2 = 0, we have e = (e / 2) * 2
  // Therefore 2 * (e / 2) = (e / 2) * 2 = e
  ()  // The F* solver can handle this simple arithmetic reasoning

(* Prove that double is surjective onto even integers *)
let double_surjective() : Lemma (forall (e:even_int). double (half e) == e) =
  let lemma_for_each_even (e:even_int) : Lemma (double (half e) == e) =
    calc (==) {
      double (half e);
      == {}
      op_Multiply 2 (e / 2);
      == { lemma_double_half_even e }
      e;
    }
  in
  FStar.Classical.forall_intro lemma_for_each_even
