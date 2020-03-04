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

let f = let x = ref (-40) in
        function () ->
            (x:=!x+41;!x)
 in (f ()) * (f ());;

