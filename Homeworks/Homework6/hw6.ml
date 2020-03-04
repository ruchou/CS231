(*Q1*)

(*Qa*)
let r = ref 41 in
    let x = (r := !r+1)   in
        !r ;;

(*Qb*)
let r = ref 41 in
let x = ((function r -> (r := 41; 500)) (let _ = (r := !r+1) in ref !r )) in
!r;;

(*Qc*)


let fact = ref (function x -> x + 1) in
    let _ = fact := (function x -> if x = 0 then 1 else x * !fact(x-1)) in
        !fact ;;


let f = let x = ref (-40) in
        function () ->
            (x:=!x+41;!x)
 in (f ()) * (f ());;

