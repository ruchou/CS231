
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

let rec typecheck (t:t) (env:env) : typ = match t with
    | True -> Bool
    | Function (x, xType, term) ->(try
        let t2 = typecheck term ((x,xType)::env) in
            Arrow(xType, t2)
        with TypeError -> raise TypeError
        )
    | FunCall (t1 , t2) -> ( match (typecheck t1 env) with
        | Arrow (t2_ , t_) -> if (typecheck t2 env) = t2_ then t_ else raise TypeError
        | _ -> raise TypeError )
    | Var x ->(try
                (List.assoc x env)
            with Not_found -> raise TypeError)
    | _ -> raise TypeError
    ;;
(*((\x:Bool -> x) True)*)
let t1 =  FunCall(Function("x",Bool,Var "x") ,True) in
    assert(typecheck t1 [] = Bool)
    ;;

let t2 = Function("x",Bool,Var "x") in
    assert(typecheck t2 [] = Arrow(Bool,Bool))
    ;;

(*(\x:(\y:Bool -> y) -> x)(\y:Bool -> y )*)
let t3 = FunCall(Function("x",Arrow(Bool,Bool), Var "x"),Function("y",Bool, Var "y")) in
    assert(typecheck t3 [] = Arrow(Bool,Bool))
    ;;

let t4 = FunCall(Function("x",Arrow(Arrow(Bool,Bool),Arrow(Bool,Bool)), Var "x"),Function("y",Arrow(Bool,Bool), Var "y")) in
    assert(typecheck t4 [] = Arrow (Arrow (Bool, Bool), Arrow (Bool, Bool)))
    ;;

let t5 = Var "joe" in
    assert(typecheck t5 [("joe",Bool)] = Bool)
    ;;