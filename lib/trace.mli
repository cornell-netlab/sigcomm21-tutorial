open Coq_minip4.Syntax

type t = 
  | Input of exp
  | Output of exp
  | Extract of name * exp
  | Emit of name * exp
  | Assign of name * exp
  | TableAction of name * int

val map_exp : (exp -> exp) -> t -> t

val format_t : t -> 'a Pp.t
