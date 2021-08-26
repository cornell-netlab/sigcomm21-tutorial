open Coq_minip4.Syntax

let repeat x n = 
  if n < 0 then 
    failwith "Unexpected error: expected non-negative integer";
  let rec loop acc n = 
    match n with 
    | 0 -> acc
    | _ -> loop (x::acc) (n - 1) in 
  loop [] n

let bits_of_hexstring hex length = 
  let rec loop acc n i = 
    if i = 0 then 
      acc
    else
      let b = if Int32.rem n 2l = 0l then false else true in 
      loop (b::acc) (Int32.shift_right n 1) (i - 1) in 
  loop [] (Int32.of_string hex) length

let intstring_of_bits bits = 
  let to_bit b = if b then "1" else "0" in
  List.map to_bit bits |> 
  String.concat "" |> 
  (fun s -> "0b" ^ s) |> 
  Int32.of_string |> 
  Int32.to_string 

let mk_concat_typ t1 t2 = 
  match t1,t2 with 
  | Unit,t
  | t, Unit -> t
  | _ -> Prod(t1,t2)

let mk_concat e1 e2 = 
  match e1,e2 with 
    | Tt,e 
    | e,Tt -> e
    | _ -> Tuple(e1,e2)
