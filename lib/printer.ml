open Pp
open Pp.O
open Coq_minip4.Syntax

let format_int (i: int) : 'a Pp.t =
  i
  |> string_of_int
  |> text

let format_binop (b: binop) : 'a Pp.t =
  match b with
  | Eq -> text " == "
  | Neq -> text " != "

let format_uop (u: uop) : 'a Pp.t =
  match u with
  | Hash -> text "hash"
  | Sum -> text "sum"

let format_bit (b: bool) : 'a Pp.t =
  if b
  then text "1"
  else text "0"

let format_bitstring (bs: bitstring) : 'a Pp.t =
  text "0b"
  ++ concat_map ~f:format_bit bs

let rec format_exp (e: exp) : 'a Pp.t =
  match e with
  | Var x ->
     text x
  | EBool b ->
     if b
     then text "true"
     else text "false"
  | Bits b ->
     format_bitstring b
  | Tuple (e1, e2) ->
     text "("
     ++ format_exp e1
     ++ verbatim ", "
     ++ format_exp e2
     ++ text ")"
  | Tt -> text "tt"
  | Proj1 e ->
     format_exp e ++ text ".1"
  | Proj2 e ->
     format_exp e ++ text ".2"
  | BinOp (b, e1, e2) ->
     format_exp e1
     ++ format_binop b
     ++ format_exp e2
  | UOp (u, e) ->
     format_uop u
     ++ text "("
     ++ format_exp e
     ++ text ")"
