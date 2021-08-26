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
  | Tuple(e1,e2) -> 
     let typ1 = typ_of_exp typ_env e1 in
     let typ2 = typ_of_exp typ_env e2 in
     Prod(typ1, typ2)
  | Proj1(e) -> 
     begin 
       match typ_of_exp typ_env e with 
       | Prod(typ1,_) -> typ1
       | _ -> failwith "Unexpected typ for projection"
     end
  | Proj2(e) -> 
     begin 
       match typ_of_exp typ_env e with 
       | Prod(_,typ2) -> typ2
       | _ -> failwith "Unexpected typ for projection"
     end
  | Tt -> 
     Unit
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
