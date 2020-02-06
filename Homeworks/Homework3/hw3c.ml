
(* Problem 3 *)

(* T ::= Bool | T -> T *)
type typ = Bool | Arrow of typ * typ

(* t ::= true | x | lambda x:T.t | t1 t2 *)
type t = True | Var of string | Function of string * typ * t 
       | FunCall of t * t


(* env is a **type alias** for a list of (string,typ) pairs 
   env is not a new type, like t above, 
   but rather just a name for an existing type. 

   a list of pairs is sometimes called an *association* list.
   OCaml already has some useful operations for manipulating such lists.
   In particular, the function List.assoc (in the List standard library)
   looks up the value associated with a given key in a given association
   list.  e.g., List.assoc "y" [("x", Bool); ("y", Arrow(Bool,Bool))]
   returns Arrow(Bool,Bool).  List.assoc raises a Not_found exception
   if the given key is not in the list.

*)
type env = (string * typ) list

exception TypeError

(* typecheck takes a term (of type t) and a type environment (of type env) 
   and it returns the type of the term, or raises TypeError if the term
   cannot be given a type.  this function should have the same behavior
   as the typechecking rules on the cheat sheet. *)
let rec typecheck (t:t) (env:env) : typ = raise TypeError
