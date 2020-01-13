

let rec power f n =
    let compose f g  = fun x -> f (g x) in
        if n =  0 then fun x -> x
        else compose f ( power f (n-1))
        ;;

let f x = x  in
    power f 10;;
