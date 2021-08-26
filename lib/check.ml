open Coq_minip4.Syntax

let rec typ_of_exp (typ_env:typ Env.StringMap.t) (e:exp) : typ = 
  match e with 
  | Var(x) -> 
     begin 
       try 
         Env.StringMap.find x typ_env
       with Not_found ->
         failwith "Unexpected error: unbound variable"
     end
  | EBool(_) -> Bool
  | Bits(bs) -> Bit (List.length bs)
  | Tuple(es) -> Prod(List.map (typ_of_exp typ_env) es)
  | Proj(e,n) -> 
     begin 
       match typ_of_exp typ_env e with 
       | Prod(ts) -> List.nth ts (n - 1)
       | _ -> failwith "Unexpected typ for projection"
     end
  | BinOp(_, t1, t2) -> 
     let typ1 = typ_of_exp typ_env t1 in
     let typ2 = typ_of_exp typ_env t2 in
     if typ1 <> typ2 then 
       failwith "Unexpected error: incompatible types in binary operation"
     else 
       typ1
  | UOp(_, t1) -> 
     let _ = typ_of_exp typ_env t1 in 
     (* TODO: the return type might vary depending on the operator  *)
     Bit(8)
