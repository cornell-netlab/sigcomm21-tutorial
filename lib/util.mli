open Coq_minip4.Syntax

val repeat : 'a -> int -> 'a list
val bits_of_hexstring : string -> int -> bool list
val intstring_of_bits : bool list -> string
val mk_concat : exp -> exp -> exp
val mk_concat_typ : typ -> typ -> typ
