let value : int ref = ref 0
let gensym () =
  value := !value + 1;
  string_of_int !value