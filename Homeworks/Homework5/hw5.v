(* Homework 5 *)
(*Yan-Ru Jhou and Nurrachman Liu*)
(* Due by the end of the day on March 3.  Just turn in this file. *)

(* Here are the type definitions for booleans and natural numbers,
   along with a function for addition, that we saw in class. *)

Inductive bool : Type :=
  true : bool
| false : bool.

Inductive nat : Type :=
  zero : nat
| succ : nat -> nat.

Fixpoint plus (n1 n2 : nat) : nat :=
  match n1 with
    zero => n2
  | succ n1' => succ (plus n1' n2)
  end.

(* PROBLEM 1: Prove the following lemma about addition. Remove "Admitted." and replace it with your proof. *)  

Lemma plus_succ_right : forall n1 n2, 
  succ (plus n1 n2) = plus n1 (succ n2).
Proof.
  intros n. intros m. induction n as [|n'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.


(* PROBLEM 2a: Define the following function, which doubles the given natural number.  Don't call any helper functions; instead directly define the function recursively. Some example tests are shown below.  Remove "Admitted." and fill in the body of the double function before the period.
*)

Fixpoint double (n : nat) : nat :=
  match n with
    zero => zero
    |succ n' => plus (succ n') (succ n')
  end.

Definition one := succ zero.
Definition two := succ one.
Definition three := succ two.
Definition four := succ three.

(* After defining double above, you should be able to remove "Admitted." below, uncomment the proofs, and everything should work without errors. *)
Example doubleZero : double zero = zero.
Proof.
  reflexivity.
Qed.
Example doubleOne : double one = two.
Proof.
  reflexivity.
Qed.

Example doubleTwo : double two = four.
Proof.
  reflexivity.
Qed.
(* Proof. reflexivity. Qed. *)

(* PROBLEM 2b: Prove the following lemma about doubling and addition. HINT: Your proof will make use of the lemma you proved in Problem 1 above. Remove "Admitted." and replace it with your proof. *)

Lemma doublePlus : 
  forall n, (double n) = (plus n n).
Proof.
  intros. 
  destruct n.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* PROBLEM 3a: Complete the definition of the proposition leq below such that (leq n m) is provable if and only if n <= m, where n and m are of type nat.  Don't make any helper functions or types.  *)

Inductive leq : nat -> nat -> Prop :=
  LeqZero: forall n, leq zero n
  |LeqS: forall n1 n2, leq n1 n2 -> leq (succ n1) (succ n2)
. 

(* PROBLEM 3b: Build a derivation of the proposition (leq two four). Remove "Admitted." and provide the definition of two_leq_four. *)

Example two_leq_four : leq two four.
Proof.
  apply LeqS. apply LeqS. apply LeqZero.
Qed.
(* PROBLEM 3c:  Prove this lemma about leq
and plus. Remove "Admitted." and replace it with your proof. *)    

Lemma leq_plus : forall n1 n2,
  leq n1 (plus n1 n2).
Proof.
  intros n1 n2 . induction n1 as [|n1'].
  -simpl. apply LeqZero.
  -simpl. apply LeqS. assumption.
Qed.

(* PROBLEM 4: CS231 All Over Again *)

(* Problem 4a: Add the syntax for natural number constants (making use of the nat type defined earlier) and addition to our grammar, i.e.: 
      t ::= ... | n | t1 + t2
*)

Inductive term : Type :=
| t_unit : term
| t_true : term
| t_false : term
| t_if : term -> term -> term -> term
| t_num : nat -> term
| t_plus : term -> term -> term.

(* Problem 4b: Add the type Nat for natural numbers to our definition of types below. *)

Inductive ty : Type :=
| Unit : ty
| Bool : ty
| Nat : ty.

(* Problem 4c: Add typing rules for your new terms. *)

Inductive typeof : term -> ty -> Prop :=
| tcUnit : typeof t_unit Unit
| tcTrue : typeof t_true Bool
| tcFalse : typeof t_false Bool
| tcIf : forall t1 t2 t3 T, typeof t1 Bool -> typeof t2 T -> typeof t3 T -> typeof (t_if t1 t2 t3) T
| tcNum: forall n, typeof (t_num n) Nat
| tcPlus: forall t1 t2, typeof t1 Nat -> typeof t2 Nat -> typeof (t_plus t1 t2) Nat.



Notation "t : T" := (typeof t T) (at level 40). 

(* Problem 4d: Add natural number constants as a kind of value. *)

Inductive isValue : term -> Prop :=
| unitVal : isValue t_unit
| trueVal : isValue t_true
| falseVal : isValue t_false
| numVal: forall n, isValue (t_num n). 

(* Problem 4e: Add the operational semantics for your new terms, using the same semantics that we've done previously for integer terms. *)

Inductive step : term -> term -> Prop :=
  | stepIfTrue : forall t2 t3, step (t_if t_true t2 t3) t2
  | stepIfFalse : forall t2 t3, step (t_if t_false t2 t3) t3
  | stepIf :
    forall t1 t1' t2 t3,
      step t1 t1' -> step (t_if t1 t2 t3) (t_if t1' t2 t3)
  | stepPlus1:
    forall t1 t1' t2, step t1 t1' -> step (t_plus t1 t2) (t_plus t1' t2)
  | stepPlus2:
    forall n1 t2 t2', step t2 t2' -> step (t_plus n1 t2) (t_plus n1 t2')
  | stepPlusRed:
    forall n1 n2, step (t_plus (t_num n1) (t_num n2)) ( t_num (plus n1 n2) ).


Notation "t1 '-->' t2" := (step t1 t2) (at level 40).

(* Problem 4f: Complete the Progress proof for your language. This will also require updating the cfBool lemma and adding a new Canonical Forms lemma for type Nat. *)

Lemma cfBool : forall v, isValue v -> v : Bool -> v = t_true \/ v = t_false.
Proof.
  intros. inversion H.
  - rewrite <- H1 in H0. inversion H0.
  - left. reflexivity.
  - right. reflexivity.
  - rewrite <-H1 in H0. inversion H0.
Qed.

Lemma cfNat: forall v, isValue v -> v : Nat -> exists n, v = t_num n.
Proof.
  intros. inversion H.
  - rewrite <-H1 in H0. inversion H0.
  - rewrite <-H1 in H0. inversion H0.
  - rewrite <-H1 in H0. inversion H0.
  - exists n. reflexivity. 
Qed.


Theorem progress : forall t T, t : T -> isValue t \/ exists t', t --> t'.
Proof.
  intros. induction H.
  - left. apply unitVal.
  - left. apply trueVal.
  - left. apply falseVal.
  - right. inversion IHtypeof1.
    *  apply (cfBool t1 H2) in H. inversion H.
      + exists t2. rewrite H3. apply stepIfTrue.
      + exists t3. rewrite H3. apply stepIfFalse.
    * inversion H2. exists (t_if x t2 t3). apply stepIf. apply H3.
  - left. apply numVal.
  - right. inversion IHtypeof1.
    *apply cfNat in H1. inversion H1. inversion IHtypeof2.
      + apply cfNat in H3. inversion H3. exists (t_num (plus x x0)). rewrite H2. rewrite H4. apply stepPlusRed. apply H0.
      + inversion H3. inversion H3. exists (t_plus t1 x0). rewrite H2. apply stepPlus2. assumption.
      + assumption.
    * inversion H1. exists(t_plus x t2). apply stepPlus1. assumption.
      
Qed.

(* Problem 4g: Complete the Preservation proof for your language. *)

Theorem preservation : forall t t' T, t : T -> t --> t' -> t' : T.
Proof.
  intros. generalize dependent t'. induction H.
  - intros. inversion H0.
  - intros. inversion H0.
  - intros. inversion H0.
  - intros. inversion H2.
    * rewrite <- H3. assumption.
    * rewrite <- H3. assumption.
    * apply tcIf.
      + apply IHtypeof1. assumption.
      + assumption.
      + assumption.
  - intros. inversion H0.
  - intros. inversion H1.
    * apply tcPlus. apply IHtypeof1. assumption. assumption.
    * apply tcPlus. assumption. apply IHtypeof2. assumption.
    * apply tcNum.
 Qed.
