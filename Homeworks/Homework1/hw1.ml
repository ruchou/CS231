
exception ImplementMe

type t = True | False | If of t * t * t | Int of int | Plus of t * t | Greater of t * t

let isval t =
  match t with
      True|False -> true
    | Int _ -> true
    | _ -> false

(* Problem 1a.  *)

exception NormalForm 

let rec step t = raise ImplementMe


(* Problem 1b. *)
  
let rec eval t = raise ImplementMe

