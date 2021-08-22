open Coq_minip4.Syntax

let print (e: exp) : unit =
  match e with
  | EBool(Coq_true) -> Printf.printf "true"
  | EBool(Coq_false) -> Printf.printf "false"
  | _ -> failwith "unimplemented"

