type mybool = True | False;;

let myand b1 b2 = match b1 with
    |True -> b2
    |False -> False
    ;;

myand True False;;


let ctrue = (function t -> function  f -> t) ;;
let cfalse = (function t -> function  f -> f) ;;

let cand b1 b2 = b1 b2 cfalse ;;

(cand ctrue cfalse) true false;;




let czero = (function z -> function s -> z);;
let cOne = (function z -> function s -> s z);;
let cTwo = (function z -> function s -> s (s z));

let cplus n1 n2 =
    (function z -> function s -> n1 (n2 z s ) s );;
     //call successor from zero to n2
     //then call success from n2 to n2
     // n1 + n2



