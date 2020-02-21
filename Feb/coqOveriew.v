

(* euqivalent Ocaml: type bool = True | False  *)

Inductive bool: Type :=
    true:bool
   |false:bool.

Definition negate (b:bool) :=
    match b with
        true => false
       | false => true

    end.

Compute (negate true).

Lemma doubleNegation
    : forall b , negate(negate b) = b .

Proof.

