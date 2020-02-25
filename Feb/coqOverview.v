
(* We've done manual proofs this quarter to learn how to do proofs, but they
are tedious!  For getting "real work" done, it's useful to use a proof assistant, which can prove some of the simpler parts automatically, keeps track of where you are in the proof, and checks the result. *)

(* Coq is a popular one. It is based on the Curry-Howard isomorphism, so
proving is actually a form of programming, where the theorems are expressed
as types. *)

(* The key is a flexible kind of datatype mechanism, which can declare tree structures that correspond to syntax grammars, as we've already been doing in OCaml, but also tree structures that correspond to inference rules. *)

(* Here are some traditional examples of what inductive datatypes can express. *)

(* equivalent OCaml: type bool = True | False *)
Inductive bool : Type :=
   true : bool
|  false : bool.

(* And you can define functions on these datatypes as in OCaml. *)

Definition negate (b : bool) :=
    match b with
      true => false
    | false => true
    end.

(* Such functions can be executed, in a slightly odd syntax. *)

Compute (negate true).

(* But Coq also has a proof system, so we can prove properties of our data structures and functions. Coq has a set of *tactics*, which are proof strategies, and you can write your own in a special tactic language. *)

(* A simple proof. *)

Lemma doubleNegation : forall b, negate (negate b) = b.
Proof.
  (* instantiate universally quantified values *)
  intros. 
  (* do a case analysis on the form of b *)
  destruct b. 
  - unfold negate. reflexivity. 
  - (* simpl does unfolding and more *) simpl. reflexivity.
Qed.

(* By the Curry-Howard isomorphism, doubleNegation is a function that,
   given a boolean b, produces a proof that (negate (negate b)) = b. *)
Print doubleNegation.

(* You can also write recursive types and functions, of course. *)

Inductive list : Type :=
  nil : list
| cons : bool -> list -> list.

(* Recursive definitions are written with the keyword Fixpoint. *)
Fixpoint append (l1 l2 : list) :=
  match l1 with
    nil => l2
  | cons b l1' => cons b (append l1' l2)
  end.

Compute (append (cons true nil) (cons false (cons true nil))).

(* Now proofs need induction! *)
Lemma appendToNil: forall l, (append l nil) = l.
Proof.
  intros. 
  (* induction is like destruct but also provides an induction hypothesis. *)
  (* the "as" clause is optional and just lets us use nice variable names. *)
  induction l as [|b l'].
  - simpl. reflexivity.
  - simpl. 
    (* rewrite applies a known equality to the goal *)
    rewrite IHl'. 
    reflexivity.
Qed.


(* Further, you can "extract" your Coq code to OCaml (and other languages).  So you can prove it correct and then translate to correct-by-construction OCaml code.
*)
Require Coq.extraction.Extraction.
Extraction Language OCaml.

Extraction append.

(* Here's another example proof. *)

Lemma appendAssoc: forall l1 l2 l3, 
  append l1 (append l2 l3) 
    = append (append l1 l2) l3.
Proof.
 intros. induction l1 as [|b l1'].
 - simpl. reflexivity.
 - simpl. rewrite IHl1'. reflexivity.
Qed.
