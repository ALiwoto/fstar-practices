module FunctionSurjectivity

// open FStar.Math.Lemmas

(* Define even integers *)
type even_int = n:int{n % 2 == 0}

(* Our function: double any integer *)
let double (x:int) : even_int = (op_Multiply 2 x)

(* Witness function: for any even integer, find a preimage *)
let half (e:even_int) : int = (e / 2)

(* Prove that double is surjective onto even integers *)
let double_surjective() : Lemma (forall (e:even_int). double (half e) == e) =
  let lemma_for_each_even (e:even_int) : Lemma (double (half e) == e) =
    calc (==) {
      double (half e);
      == {}
      op_Multiply 2 (e / 2);
      == { FStar.Math.Lemmas.division_multiplication_lemma e 2 }
      e;
    }
  in
  FStar.Classical.forall_intro lemma_for_each_even
