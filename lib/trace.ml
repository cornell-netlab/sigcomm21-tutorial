open Coq_minip4.Syntax
open Pp
open Pp.O

type t = 
  | Input of exp
  | Output of exp
  | Extract of name * exp
  | Emit of name * exp
  | Assign of name * exp
  | TableAction of name * int

let format_t (t:t) : 'a Pp.t = 
  match t with 
  | Input(e) -> 
     verbatim "[ Input       ] " ++ Printer.format_exp e
  | Output(e) -> 
     verbatim "[ Output      ] " ++ Printer.format_exp e
  | Extract(x,e) -> 
     verbatim "[ Extract     ] " ++ verbatim x ++ verbatim " = " ++ Printer.format_exp e
  | Emit(x,e) -> 
     verbatim "[ Emit        ] " ++ verbatim x ++ verbatim " = " ++ Printer.format_exp e
  | Assign(x,e) -> 
     verbatim "[ Assign      ] " ++ verbatim x ++ verbatim " = " ++ Printer.format_exp e
  | TableAction(x,n) ->
     verbatim "[ TableAction ] " ++ verbatim x ++ text "." ++ Printer.format_int n

let map_exp f t = 
  match t with
  | Input(e) -> Input(f e)
  | Output(e) -> Output(f e)
  | Extract(x,e) -> Extract(x,f e)  
  | Emit(x,e) -> Emit(x,f e)
  | Assign(x,e) -> Assign(x, f e)
  | TableAction _ -> t
