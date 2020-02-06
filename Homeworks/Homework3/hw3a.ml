exception ImplementMe

(* Problem 1 *)  
  
(* Type t represents abstract syntax trees for the lambda calculus.  A
variable name is represented as an OCaml string. We include the value
True so that you have a simple value to use for testing purposes.

Example: the term ((func)tion x -> x x) (function x -> x)) would be represented as follows:

   FunCall(Function("x", FunCall(Var "x", Var "x")), Function("x", Var "x")

*)

type t = True | Var of string | Function of string * t | FunCall of t * t
	
(* 1a: Implement the subst function below, which substitutes a given
   value v for all free occurrences of the variable named x in term t,
   returning the resulting term. You may assume that v has no free
   variables. *)

let rec subst (x:string) (v:t) (t:t) = match t with
    | True -> True
    | Var x' -> if x'=x then v else t
    | Function (x0, t1) -> if x0=x
        then  Function (x0, t1)
        else Function(x0, subst x v t1)
    | FunCall (t1,t2) -> FunCall (subst x v t1,subst x v t2)
    ;;

  
(* 1b: Implement the step function, which takes a term of type t above
and produces a new term that results from taking one step of
computation on t, following the operational semantics rules for the 
lambda calculus.  If t is a normal form, the step function should
raise the NormalForm exception declared below. *)

exception NormalForm  

let isval t =
  match t with
    |True -> true
    | Function(_,_) -> true
    | _ -> false
    ;;
let rec step t = match t with
    | FunCall(t1,t2) ->( match t1 with
        | Function (x,t3) -> match isval t2 with
            | true -> subst x t2 t3
            | false -> FunCall (t1, step t2)
        | _ -> FunCall (step t1, t2))
    | _ -> raise NormalForm
    ;;


(*Test cases*)
(*TestCases for if else*)
(*Example: the term (function x -> x x) (function x -> x)) would be represented as follows:*)
(*   FunCall(Function("x", FunCall(Var "x", Var "x")), Function("x", Var "x")*)
let c1 = FunCall(Function("x", FunCall(Var "x", Var "x")), Function("x", Var "x")) in
        assert(step c1 = FunCall (Function ("x", Var "x"), Function ("x", Var "x")));;
(*(\x -> x )(\y->y)*)
let c2 = FunCall(Function("x",Var "x"),Function("y",Var "y")) in
    assert(step c2 = Function("y",Var "y"));;

(*(\x -> x )(true)*)
let c3 = FunCall(Function("x",Var "x"),True) in
    assert(step c3 = True);;

(*(\x -> x )(\y-> \z -> y )*)
let c4 = FunCall(Function("x",Var "x"),Function("y",Function("z",Var "z" ))) in
    assert(step c4 = Function ("y", Function ("z", Var "z")));;

(*(\x -> \x -> x*)
(*let c4 = Function("x",Function("x", Var "x" )) in*)
(*    assert(step c4 = Function ("y", Function ("z", Var "z")));;*)

(*(* True )(\y-> \z -> y )*)*)
(*let c5 = FunCall(True,Function("y",Function("z",Var "z" ))) in*)
(*    assert(step c4 = Function ("y", Function ("z", Var "z")));;*)

(*(\q -> q q)(True)*)
let c6 = FunCall(Function("q", FunCall(Var "q",Var "q")),True) in
    assert(step c6 = FunCall(True,True))
    ;;