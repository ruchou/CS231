
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

(* We've seen functions that take values and return values, like all languages have.  *)

(* Coq also has functions that take types and return values.  That gives you the expressiveness to define explicit parametric polymorphism. For example, here is a polymorphic identity function. *)

Definition id (T : Type) (x : T) := x.

(* Its type is forall T, T -> T. *)
Check id.

Compute id bool false.
Compute id (bool -> bool) negate.

(* Explicit polymorphism is more powerful than the implicit let-polymorphism of OCaml.  For example, id can be passed to itself. *)

Compute id (forall T, T->T) id.

(* More weirdly, in Coq you can also define *type functions*.  For example, you can write functions that take types and return types. This gives us the ability to define polymorphic types.  For example, here is a version of lists that is polymorphic over the element type. *)

Module PolyLists.

Inductive list (T : Type) : Type :=
  nil : list T
| cons : T -> list T -> list T.

Compute cons bool false (nil bool).

Compute cons (bool -> bool) negate (nil (bool -> bool)).

(* As another example, here's a polymorphic type for pairs. *)
Inductive pair (A : Type) (B : Type) : Type :=
  p : A -> B -> pair A B.

End PolyLists.

(* Ok, so we have functions from values to values, types to values, and types to types.  What's left?  Functions from values to types.  These are called *dependent types*.  As an example, we'll define natural numbers, and then define a list type that is parameterized by a natural number, representing the list's length. *)

Inductive nat : Type :=
  zero : nat
| succ : nat -> nat.

Fixpoint plus (n1 n2 : nat) : nat :=
  match n1 with
    zero => n2
  | succ n1' => succ (plus n1' n2)
  end.
Module ListsWithLength.

(* Here's the cool thing:  The datatype definition for list below is written in such a way that it is only possible to build lists that are properly annotated with their correct length.  (For simplicity we went back to lists of booleans, but we could also make them polymorphic over the element type as well.)
*)


Inductive list : nat -> Type :=
  nil : list zero 
| cons : forall n, bool -> list n -> list (succ n).

Compute (cons (succ zero) true (cons zero false nil)).

(* Now you can also define list operations and use their dependent types to ensure properties about their length.  For example, here we re-define the append function from earlier, but now its type ensures that the length of (append l1 l2) is the sum of the lengths of l1 and l2.  *)

Fixpoint append n1 n2 (l1 : list n1) (l2 : list n2) : list (plus n1 n2) :=
  match l1 with
    nil => l2
  | cons n1' b l1' => cons (plus n1' n2) b (append n1' n2 l1' l2)
  end.


End ListsWithLength.

(* Why do we care about lists that know their length?  Well, dependent types are interesting in their own right.  But for our purposes, the key is that this mechanism lets us define inference rules!

Coq has two (actually three but we'll ignore one of them) different *sorts*,which are like the types of types:
   - Type is the sort of types like nat and list, which in turn classify data (syntax trees).
   - Prop classifies propositions, which in turn classify proofs (derivation trees).
   
By the Curry-Howard Isomorphism they are the same thing, but Coq keeps them separate since they are used for different purposes.
*)

(*

Consider a proposition (isEven n), which should be provable only when n is even.  Here are the inference rules that you would write:

---------------- EvenZ
isEven zero


isEven n
----------------------- EvenS
isEven (succ (succ n))

Here's how we can write those inference rules in Coq.  Note how we use dependent types to enforce that we can only build trees that correspond to valid derivations through our rules.
*)

Inductive isEven : nat -> Prop :=
  EvenZ : isEven zero
| EvenS : forall n, isEven n -> isEven (succ (succ n)).

(* We can now build derivation trees using these rules. *)

Definition isEvenFour : isEven (succ (succ (succ (succ zero)))) :=
  EvenS (succ (succ zero)) (EvenS zero EvenZ).

(* We can also use tactics to build derivation trees. *)

Example fourIsEven : isEven (succ (succ (succ (succ zero)))).
Proof.
  apply EvenS. apply EvenS. apply EvenZ.
Qed.

Print fourIsEven.


(* Ok, great. Now we have seen everything that we need in order to do CS231 using Coq.  First let's define the syntax of terms for a language of booleans, similar to how we did in OCaml. We will add unit so it's not totally trivial. *)


Inductive term : Type :=
| t_unit : term
| t_true : term
| t_false : term
| t_if : term -> term -> term -> term.

(* As usual we can build terms that meet this grammar. *)

Definition simpleTerm := t_if t_true t_false t_true.
Print simpleTerm.

(* Now the grammar for types *)

Inductive ty : Type :=
| Unit : ty
| Bool : ty.


(* Now we'll do something analogous to our isEven proposition above to define the type rules for this language.  The following typeof judgment is the implementation of our t:T judgment. *)

Inductive typeof : term -> ty -> Prop :=
| tcUnit : typeof t_unit Unit
| tcTrue : typeof t_true Bool
| tcFalse : typeof t_false Bool
| tcIf : forall t1 t2 t3 T, typeof t1 Bool -> typeof t2 T -> typeof t3 T -> typeof (t_if t1 t2 t3) T.

(* We can even use the same notation as we normally do. *)
Notation "t : T" := (typeof t T) (at level 40). 

(* Now we can build typing derivations, manually and using tactics. *)

Definition simple := t_if t_true t_false t_true.

Definition tcSimple : (typeof simple Bool) :=
  tcIf t_true t_false t_true Bool tcTrue tcFalse tcTrue.

Example simpleTypechecks : typeof simple Bool.
Proof.
  unfold simple. apply tcIf. apply tcTrue. apply tcFalse. apply tcTrue.
Qed.

Print simpleTypechecks.

(* Let's do the same thing to define the operational semantics. We normally use a grammar for values, but we'll do it here as a set of inference rules.  (You could instead do it as a function, as we did in OCaml.) *)

Inductive isValue : term -> Prop :=
| unitVal : isValue t_unit
| trueVal : isValue t_true
| falseVal : isValue t_false.

Inductive step : term -> term -> Prop :=
  | stepIfTrue : forall t2 t3, step (t_if t_true t2 t3) t2
  | stepIfFalse : forall t2 t3, step (t_if t_false t2 t3) t3
  | stepIf :
    forall t1 t1' t2 t3,
      step t1 t1' -> step (t_if t1 t2 t3) (t_if t1' t2 t3).

Notation "t1 '-->' t2" := (step t1 t2) (at level 40).

(* Now we can interact to prove type soundness! *)

Lemma cfBool : forall v, isValue v -> v : Bool -> v = t_true \/ v = t_false.
Proof.
  intros. inversion H.
  - rewrite <- H1 in H0. inversion H0.
  - left. reflexivity.
  - right. reflexivity.
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
Qed.


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
Qed.