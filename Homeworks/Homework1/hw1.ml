
exception ImplementMe

type t = True | False | If of t * t * t | Int of int | Plus of t * t | Greater of t * t

let isval t =
  match t with
      True|False -> true
    | Int _ -> true
    | _ -> false

(* Problem 1a.  *)

exception NormalForm 

let rec step t = match t with
    | If (True,t2,_) -> t2 (*E-IFTrue*)
    | If (False,_,t3) -> t3 (*E-IFFalse*)
    | If (t1,t2,t3) -> If ((step t1),t2,t3) (*E-IF*)
    | Plus (Int n1,Int n2) -> Int (n1+n2) (*E-Plus*)
    | Plus (t1,t2) when isval t1 = true -> Plus (t1, step t2 ) (*E-IFPlus2*)
    | Plus (t1,t2) -> Plus ( step t1,t2 ) (*E-IFPlus1*)
    | Greater (Int n1,Int n2) -> if n1 > n2 then True else False (*E-GT*)
    | Greater (t1,t2) when isval t1 -> Greater(t1, step t2) (*E-GT1*)
    | Greater (t1, t2) -> Greater (step t1,t2) (*E-GT1 *)
    | _ -> raise NormalForm
    ;;


(* Problem 1b. *)
  
let rec eval t =
    try eval (step t)
    with
        NormalForm -> t
     ;;


(*Test cases*)
(*TestCases for if else*)
let case1 = assert(step(If(True, False, True)) = False) ;;
let case2 = assert(step(If(False, False, True)) = True) ;;
let case3 = If(If(True,False,False),True,False) in
    assert(step(case3) =  If(False, True, False));
    assert((eval case3) = False);;
let case4 = If(True,(Int 1),False ) in
    assert(step(case4) = Int 1);
    assert(eval case4 = Int 1);;
let case5 = If(False,(Int 1),True ) in
    assert(step(case5) = True);
    assert(eval case5 = True);;
(*TestCases for Plus*)

let case6 = Plus (Int 1, Int 5) in
    assert(step case6  = Int 6);
    assert(eval case6 = Int 6);;
let case7 = Plus ( If(True,Int 6, Int 7), Int 8 ) in
    assert(step case7 = Plus(Int 6,Int 8));
    assert(eval case7 = Int 14);;
let case8 = Plus ( If(True,False, Int 7), Int 8 ) in
    assert(step case8 = Plus(False,Int 8));
    assert(eval case8 = Plus (False,Int 8 ));;
let case9 = Plus (If(True,Int 90, Int 7),If(False,False, Int 7) ) in
    assert (step case9 = Plus (Int 90,If(False,False, Int 7)));
    assert (eval case9 = Int 97);;

(*TestCases for Greater*)
let case10 = Greater (Int 10, Int 20) in
    assert(step case10 = False);
    assert(eval case10 = False);;
let case11 = Greater ( Plus(Int 1, Int 10), Int (-1) ) in
    assert(step case11 = Greater(Int 11, Int (-1) )) ;
    assert(eval case11 = True);;
let case12 = Greater (Plus(Int 20, Int 15),If(True,Int 20,Int 30)) in
    assert(step case12 = Greater(Int 35, If(True,Int 20,Int 30))) ;
    assert(eval case12 = True);;



(*Q2*)
let q2 = If (Greater(Plus (Int 1,Int 2) , Int 3),Plus(Int 4,Int 5),Plus(Int 6, Int 7)) in
    step q2;;
