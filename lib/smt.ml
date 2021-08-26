open Coq_minip4.Syntax

type term = exp

type formula = 
  | True
  | False 
  | And of formula * formula
  | Or of formula * formula
  | Not of formula
  | Eq of term * term 
  | Neq of term * term

let ctx = Z3.mk_context [("model", "true")]

let rec z3_of_typ : typ -> Z3.Sort.sort = 
  (* Hash-cons tuple types *) 
  let prod_ctr = ref 0 in
  let prod_hash = Hashtbl.create 31 in
  let mk_tuple n = Printf.sprintf "tuple_%d" n in 
  let mk_field n i = Printf.sprintf "tuple_%d_%d" n i in   
  function
  | Bool -> 
     Z3.Boolean.mk_sort ctx
  | Bit n -> 
     Z3.BitVector.mk_sort ctx n 
  | Prod(t1,t2) -> 
     begin 
       try
         Hashtbl.find prod_hash (t1,t2)
       with Not_found ->
         let () = incr prod_ctr in
         let sort1 = z3_of_typ t1 in
         let sort2 = z3_of_typ t1 in
         let tuple_sym = Z3.Symbol.mk_string ctx (mk_tuple !prod_ctr) in
         let field1 = Z3.Symbol.mk_string ctx (mk_field !prod_ctr 1) in 
         let field2 = Z3.Symbol.mk_string ctx (mk_field !prod_ctr 2) in 
         let sort = Z3.Tuple.mk_sort ctx tuple_sym [field1;field2] [sort1;sort2] in
         let () = Hashtbl.add prod_hash (t1,t2) sort in
         sort
     end   
  | Unit -> 
     failwith "unimplemented"
    
let z3_mk_constr t = 
  let sort = z3_of_typ t in
  let func = Z3.Tuple.get_mk_decl sort in
  (fun es -> Z3.Expr.mk_app ctx func es)

let z3_mk_proj t = 
  let sort = z3_of_typ t in
  let fields = Z3.Tuple.get_field_decls sort in
  (fun e n ->
    if List.length fields < n then
      failwith (Printf.sprintf "Unexpected error: field %d not found" n)
    else
      Z3.Expr.mk_app ctx (List.nth fields (n-1)) [e])
  
let z3_of_var typ_env x = 
     let typ =
       try 
         Env.StringMap.find x typ_env 
       with Not_found ->
         failwith "Unexpected error: unbound variable" in
     let sort = z3_of_typ typ in
     Z3.Expr.mk_const_s ctx x sort

let extract_byte (e:Z3.Expr.expr) : bool list = 
  let hex = "0" ^ String.sub (Z3.Expr.to_string e) 1 3 in
  Util.bits_of_hexstring hex 8

let rec z3_of_term (typ_env:typ Env.StringMap.t) (e:exp) : Z3.Expr.expr = 
  match e with 
  | Var(x) -> 
     z3_of_var typ_env x
  | EBool(true) -> 
     Z3.Boolean.mk_true ctx
  | EBool(false) -> 
     Z3.Boolean.mk_true ctx
  | Bits(bs) -> 
     let length = List.length bs in
     let str = Util.intstring_of_bits bs in
     let res = Z3.BitVector.mk_numeral ctx str length in
     assert (extract_byte res = bs);
     res
  | Tuple(e1,e2) -> 
     let t = Check.typ_of_exp typ_env e in
     let constr = z3_mk_constr t in
     constr (List.map (z3_of_term typ_env) [e1;e2])
  | Proj1(e) -> 
     let t = Check.typ_of_exp typ_env e in
     let proj = z3_mk_proj t in
     proj (z3_of_term typ_env e) 1
  | Proj2(e) -> 
     let t = Check.typ_of_exp typ_env e in
     let proj = z3_mk_proj t in
     proj (z3_of_term typ_env e) 2
  | Tt -> 
     failwith "unimplemented"
  | BinOp(Eq, e1, e2) -> 
     Z3.Boolean.mk_eq ctx (z3_of_term typ_env e1) (z3_of_term typ_env e2)
  | BinOp(Neq, e1, e2) ->
     Z3.Boolean.mk_eq ctx (z3_of_term typ_env e1) (z3_of_term typ_env e2) |> 
       Z3.Boolean.mk_not ctx      
  | UOp(Hash, _) -> 
     assert false
  | UOp(Sum, _) -> 
     assert false

let rec z3_of_formula typ_env = function
  | True -> 
     Z3.Boolean.mk_true ctx
  | False -> 
     Z3.Boolean.mk_false ctx
  | And(p1,p2) -> 
     Z3.Boolean.mk_and ctx [z3_of_formula typ_env p1; z3_of_formula typ_env p2]
  | Or(p1,p2) -> 
     Z3.Boolean.mk_or ctx [z3_of_formula typ_env p1; z3_of_formula typ_env p2]
  | Not(p) -> 
     Z3.Boolean.mk_not ctx (z3_of_formula typ_env p)
  | Eq(t1,t2) ->
     Z3.Boolean.mk_eq ctx (z3_of_term typ_env t1) (z3_of_term typ_env t2)
  | Neq(t1,t2) -> Z3.Boolean.mk_eq ctx (z3_of_term typ_env t1) (z3_of_term typ_env t2) |> Z3.Boolean.mk_not ctx

let input_pkt = "$input"
let output_pkt = "$output"

type model = Z3.Model.model

let extract_value (typ_env:typ Env.StringMap.t) (model:model) (x:name) : exp =
  let e = Z3.Model.eval model (z3_of_var typ_env x) true |> Option.get in
  let t = Env.StringMap.find x typ_env in 
  let rec aux e t =
    match t with
    | Bit(n) -> 
       let str = Z3.Expr.to_string e in
       let hex = "0" ^ String.sub (Z3.Expr.to_string e) 1 (String.length str - 1) in
       let bs = Util.bits_of_hexstring hex n in 
       Bits(bs)
    | Bool -> 
       begin 
         match Z3.Expr.to_string e with
         | "true" -> EBool(true)
         | "false" -> EBool(false)                  
         | _ -> failwith "Unexpected error: model value is not a boolean"
       end
    | Prod(t1,t2) -> 
       let proj = z3_mk_proj t in        
       let e1 = Z3.Model.eval model (proj e 1) true |> Option.get in
       let v1 = aux e1 t1 in
       let e2 = Z3.Model.eval model (proj e 2) true |> Option.get in
       let v2 = aux e2 t2 in
       Tuple(v1,v2) 
    | Unit -> 
       Tt in
  aux e t
  
let check (typ_env:typ Env.StringMap.t) (p:formula) : model option =
  let solver = Z3.Solver.mk_simple_solver ctx in
  Z3.Solver.add solver [ z3_of_formula typ_env p ];
  match Z3.Solver.check solver [] with 
  | Z3.Solver.SATISFIABLE -> 
     begin
       match Z3.Solver.get_model solver with
       | None   -> 
          failwith "Unexpected error: model was missing"
       | Some model -> 
          Some model
     end
  | _ -> 
     None
