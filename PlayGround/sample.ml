
type my_record = {
    mutable name : string;
    id : int;
};;

let bill = ref {
    name = "bill";
    id = 35 ;
};;