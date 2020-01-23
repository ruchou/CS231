
exception ImplementMe

type t = True | False | If of t * t * t | Int of int | Plus of t * t | Greater of t * t

type typ = Bool | Integer

(* Problem 1.  *)

exception TypeError

let rec typecheck t = raise ImplementMe
