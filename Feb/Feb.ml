

let swap f = (fst f, snd f);;

let a = fst (5+5,  "hi");;



type intorbool = Left of int | Right of bool;;

Left 34;
Right true;

let toInt iorb =
    match iorb with
        Left i -> i
        |Right b -> if b then 1 else 0;;


type ('a,'b) aorb = Left of 'a | Right of 'b;;

let f pair =
    match snd pair with
        Left x1 -> (fst pair) x1
        |Right x2 -> x2;;

let f p =
    match Left p with
        Left a -> a
        | Right b -> match p with
                        Right c -> c
                        | _ -> b;;
(*         match p with*)
(*                        Right c -> c*)
(*                        |Left a_b -> a_b;;*)