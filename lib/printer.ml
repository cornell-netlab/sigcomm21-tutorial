open Coq_minip4.Syntax

let print (e: expr) : unit =
  match e with
  | NumLit _ -> failwith "unimplemented"
  | BinOp (_, _, _) -> failwith "unimplemented"
  | _ -> failwith "unimplemented"

