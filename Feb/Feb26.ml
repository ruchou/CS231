
let x = 3 in
    let x = 6 in
        x + 1;;


let x = 3 in
    let f = fun () -> x in
        let x = 6 in
            f();;

(*mutation*)

let x = 53;;

let x = ref 53;;

(*ocaml shadowing*)

let y = ref 10;;
let f() = !y;;
f();;
(*10*)
let y = ref 20;;
f();;
(*10*)

let p = ref x;;

(*you cannot change entire reference object*)

let x = ref 10;;
let y = x;;
y := 7
(*x value : 7*)


type clist = Nil | Cons of int* clist ref;;

let lst = Cons(4, ref Nil);;

let Cons(h,t) = lst in
    t := lst;;




let factorial = ref (function x -> x +1);;
factorial :=
    (function x -> if x = 0 then 1 else x* !factorial(x-1));;
!factorial(5);;


let (get,inc, reset) =
    let c = ref 0 in
       ((fun () -> !c),(fun () -> c:= !c+1),(fun ()-> c:=0));;

inc();;
get();;
reset();;
get();;
inc();;
inc();;
get();;

let makeCounter = fun () ->
    let c = ref 0 in
           ((fun () -> !c),(fun () -> c:= !c+1),(fun ()-> c:=0));;
let (get2,inc2,rest2) = makeCounter();;
let (get3,inc3,rest3) = makeCounter();;


let x = ref 0 in
    let y = ref 1 in
        let _ = (x:=1 ) in
            !y (*0*);;
