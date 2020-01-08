


(* t ::= true | false | if t then t else t
		| n | t + t | t > t
*)

(* We represent the parse trees of programs in this language
   via the following data type: *)

type t = True | False | If of t*t*t
	   | Int of int | Plus of t*t | Greater of t*t

(* what are the legal values?
	v ::= true | false | n
*)

type v = TrueVal | FalseVal | IntVal of int

exception TypeError

(* eval has type t -> v *)
let rec eval e =
	match e with
		True -> TrueVal
	 |  False -> FalseVal
	 |  If(cond, thn, els) ->
	 		(match eval cond with
	 			TrueVal -> eval thn
	 		  | FalseVal -> eval els
	 		  | _ -> raise TypeError)
	 |  Int i -> IntVal i
	 |  Plus(t1, t2) ->
	 		(match (eval t1, eval t2) with
	 			(IntVal i1, IntVal i2) -> IntVal(i1 + i2)
	 		  | _ -> raise TypeError)
	 | Greater(t1, t2) ->
	 		(match (eval t1, eval t2) with
	 			(IntVal i1, IntVal i2) ->
	 				if i1 > i2 then TrueVal else FalseVal
	 		  | _ -> raise TypeError)














