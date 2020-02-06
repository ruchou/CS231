exception ImplementMe

(* Problem 2 *)  

(* As you saw in Problem 1, implementing the lambda calculus, and any
other language that has variables, is annoying, because you have to
manually implement the means of binding variables to values, in our 
case via a substitution function.

An alternative style, known as higher-order abstract syntax (HOAS), is
a clever way to use variables from the host language (in our case,
OCaml) to represent variables in the language being implemented (in
our case, the lambda calculus).  That way, we get substitution for
free!  You will explore this style below...

*)
   
  
(* Type t represents abstract syntax trees for the lambda calculus.
We are only representing the subset of *closed* terms in the lambda
calculus -- HOAS cannot handle terms with free variables in them.
Note that we no longer have a term for variables below.  Instead,
variables are represented implicitly via the fact that a lambda
calculus function is represented as an OCaml function from terms to
terms (hence the notion of higher-order syntax -- the syntax tree
contains functions).
   
Example: the term ((function x -> x x) (function x -> x)) would be represented as follows:

   FunCall(Function(function x -> FunCall(x, x)), Function(function x -> x))

*)

type t = True | Function of (t -> t) | FunCall of t * t
	
  
(* Implement the step function, which takes a term of type t above and
   produces a new term that results from taking one step of
   computation on t.  If t is a normal form, the step function should
   raise the NormalForm exception. *)

exception NormalForm  
let isval t =
  match t with
    |True -> true
    | Function (_)  -> true
    | _ -> false
    ;;


let rec step t = match t with
    | FunCall(t1,t2) ->( match t1 with
        | Function t1' -> match isval t2 with
            | true -> t1' t2
            | false -> FunCall (t1, step t2)
        | _ -> FunCall (step t1, t2))
    | _ -> raise NormalForm
    ;;



(*testcases*)
(*Example: the term ((function x -> x x) (function x -> x)) would be represented as follows:*)

(*   FunCall(Function(function x -> FunCall(x, x)), Function(function x -> x))*)
(*let t1 =  FunCall(Function(function x -> FunCall(x, x)), Function(function x -> x)) in*)
(*    assert( step t1 =  FunCall(Function(function x -> x), Function(function x -> x)))*)

(*(\a -> a ) True*)
let t2 = FunCall(Function(function a -> a),True) in
    assert(step t2 = True)
    ;;
(*(\a -> \b -> a+b ) True*)
(*let t3 = FunCall(Function(function a -> Function(function b -> a)),True)*)
