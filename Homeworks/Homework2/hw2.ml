
exception ImplementMe

type t = True | False | If of t * t * t | Int of int | Plus of t * t | Greater of t * t

type typ = Bool | Integer

(* Problem 1.  *)

exception TypeError

let rec typecheck t = match t with
    | True -> Bool
    | False -> Bool
    | If (t1,t2,t3) -> if typecheck t1 = Bool
        then if typecheck t2 = typecheck t3
            then
                typecheck t2
             else
                raise TypeError
        else
            raise TypeError
    | Int n -> Integer
    | Plus (t1,t2) -> if typecheck t1 = Integer && typecheck t2 = Integer
        then Integer
        else
            raise TypeError
    | Greater (t1,t2) -> if typecheck t1 = Integer && typecheck t2 = Integer
        then Bool
        else
            raise TypeError
    ;;

(*Bool Test*)
let case1 = assert(typecheck True = Bool) ;;
let case2 = assert(typecheck False = Bool) ;;
let case3 = assert(typecheck False != Integer) ;;

(*Int Test*)
let case = assert(typecheck (Int 10) = Integer) ;;
let case = assert(typecheck (Int 10) != Bool) ;;

(*If Test*)
let case = assert(typecheck (If(True,True,True) ) = Bool) ;;
let case = assert(typecheck (If(True,False,True) ) = Bool) ;;
let case = assert(typecheck (If(Greater(Int 10, Int 20),False,True) ) = Bool) ;;

(*let case = assert(typecheck (If(Int 1,Int 1,True) ) = Bool) ;;*)
(*let case = assert(typecheck (If(False,Int 1,True) ) = Bool) ;;*)

(*Plus Test*)
let case = assert(typecheck (Plus(Int 1, Int 2) ) = Integer) ;;
(*let case = assert(typecheck (Plus(Int 1, True) ) = Integer) ;;*)
let case = assert(typecheck (Plus(Int 1, If(True,Int 1, Int 2)) ) = Integer) ;;

(*Greater Test*)
let case = assert(typecheck (Greater(Int 1, Int 2) ) = Bool) ;;
let case = assert(typecheck (Greater(If(False,Int 10, Int 20), Int 2) ) = Bool) ;;
(*let case = assert(typecheck (Greater(If(False,Int 10, False), Int 2) ) = Bool) ;;*)
(*let case = assert(typecheck (Greater(True, Int 2) ) = Bool) ;;*)
