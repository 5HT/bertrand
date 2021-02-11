let (>>) f g x = g (f x)

let value : int ref = ref 0
let gensym () =
  value := !value + 1;
  string_of_int !value

let rec oddEvenMap (even : 'a -> 'b) (odd : 'a -> 'c) :
    'a list -> ('b * 'c) list = function
  | a :: b :: rest ->
    (even a, odd b) :: oddEvenMap even odd rest
  | [_] -> raise (Failure "oddEvenMap")
  | [] -> []

let rec extractLast : 'a list -> 'a list * 'a = function
  | []      -> raise (Failure "extractLast")
  | [x]     -> ([], x)
  | x :: xs -> let ys = extractLast xs in (x :: fst ys, snd ys)

let pop (xs : ('a list) ref) : 'a =
  match !xs with
  | x :: xs' -> xs := xs'; x
  | [] -> raise (Failure "pop")