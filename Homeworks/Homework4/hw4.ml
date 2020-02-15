

type t = Left of string | Right of string;;

((A∨B) ∨ (C))→(A ∨ (B∨C))

fun a ->
    match p:( (A|B) | C ) with
         Left a_or_b -> match a_or_b with
                Left a ->
                   Left a
                |Right b ->
                    Left a
        | Right c ->
            R




(A \/ B) -> (B\/A)

    fun x:A \/ B->
        match x with
            left x1 -> right x1
            |right x2 -> left x2