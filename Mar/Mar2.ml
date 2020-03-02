
let fact = ref (function x -> x + 1) in
    fact := (function x -> if x = 0 then 1 else x * !fact(x-1));;


!fact 5

--->
<let fact = l in fact := (function x -> if x = 0 then 1 else x * !fact(x-1)),  {(l,ref function x->x+ 1)}>

--->
<l := (function x -> if x = 0 then 1 else x * !l(x-1)),  {(l,ref function x->x+ 1)} >
-->
<l := (function x -> if x = 0 then 1 else x * function x-1 -> x), {(l,ref function x->x+ 1)} >

-> <unit, {(l, (function x -> if x = 0 then 1 else x * function x-1 -> x))}>


let fact = ref (function x -> x + 1) in
    let _ = fact := (function x -> if x = 0 then 1 else x * !fact(x-1)) in
        !fact 5;;
