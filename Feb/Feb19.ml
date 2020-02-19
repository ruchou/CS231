

let id = (function x -> x);;

id (* int *) 24;;

let swap (x,y) = (y,x);;

    //we give the id function definition
let id = (function x -> x) in
    (id 3, id "hi");;

(*(id, V x. x-> x)*)
(*    x1 -> x1*)
(*    x2 -> x2*)

    //we dont give function definition
function id -> (id 3, id "hi") ;;
(*Error: This expression has type string but an expression was expected of type*)
(*         int*)
