open Coq_minip4.Syntax

type state = 
  { defns: defn list;
    typ_env : typ Env.StringMap.t;
    sym_env : exp Env.StringMap.t;
    extract_cur : int;
    emit_cur : int;
    path_cond : Smt.formula;
    trace : Trace.t list }

let mk_concat e1 e2 = 
  match e1,e2 with 
    | Tt,e 
    | e,Tt -> e
    | _ -> Tuple(e1,e2)

let mk_concat_typ t1 t2 = 
  match t1,t2 with 
  | Unit,t
  | t, Unit -> t
  | _ -> Prod(t1,t2)

let mtu = 4

let init_typ_env = 
  let pkt_typ = 
    let rec loop acc n = 
      if n = 0 then acc
      else loop (mk_concat_typ (Bit(8)) acc) (n-1) in
    loop Unit (mtu - 1) in

  let bindings =
    [ (Smt.input_pkt, pkt_typ);
      (Smt.output_pkt, Unit) ] in
  Env.StringMap.of_seq (List.to_seq bindings)

let init_sym_env = 
  Env.StringMap.singleton Smt.output_pkt Tt

let init_state = 
  { defns = [];
    typ_env = init_typ_env;
    sym_env = init_sym_env;
    extract_cur = 0;
    emit_cur = 0;
    path_cond = Smt.True;
    trace = [Input(Var(Smt.input_pkt))] }

let rec subst env (e:exp) : exp = 
  match e with 
  | Var(x) -> 
     (try
        Env.StringMap.find x env
      with Not_found -> 
        e)
  | EBool _ -> 
     e
  | Bits _ -> 
     e
  | Tt -> e
  | Tuple(e1,e2) -> Tuple(subst env e1,subst env e2)
  | Proj1(e) -> Proj1(subst env e)
  | Proj2(e) -> Proj1(subst env e)
  | BinOp(o,e1,e2) -> BinOp(o,subst env e1, subst env e2)
  | UOp(o,e) -> UOp(o,subst env e)

let rec simplify (e:exp) : exp = 
  match e with 
  | Var _ -> e
  | EBool _ -> e
  | Bits _ -> e
  | Tt -> e
  | Tuple(e1,e2) -> Tuple(simplify e1, simplify e2)
  | Proj1(Tuple(e1,_)) -> simplify e1
  | Proj1(e) -> Proj1(simplify e)                        
  | Proj2(Tuple(_,e2)) -> simplify e2
  | Proj2(e) -> Proj2(simplify e)                        
  | BinOp(o,e1,e2) -> BinOp(o, simplify e1, simplify e2)
  | UOp(o,e) -> UOp(o, simplify e)
              
let formula_of_exp (st:state) (e:exp) : Smt.formula =
  match Check.typ_of_exp st.typ_env e with
  | Bit(n) -> 
     Smt.Neq(e, Bits(Util.repeat false n))
  | _ -> 
     Smt.False

let rec find_table tbl defns = 
  match defns with 
  | [] -> 
     failwith "Unexpected error: could not find table" 
  | Table(tbl',keys,acts)::defns' -> 
     if tbl = tbl' then 
       (keys,acts)
     else 
       find_table tbl defns'
  | _::defns' -> 
     find_table tbl defns'

let proj_input_pkt n = 
  if n < 1 || n > mtu then 
    failwith "Unexpected error: cannot project beyond MTU";
  let rec loop acc i = 
    if i = 1 then Proj1(acc)
    else loop (Proj2(acc)) (i-1) in 
  loop (Var(Smt.input_pkt)) n
    
let rec interp_action (st:state) (act:action) : state list = 
  match act with 
  | ActNop -> [st]
  | ActSeq(act1, act2) -> 
     List.concat_map 
       (fun st1 -> interp_action st1 act2) 
       (interp_action st act1)      
  | ActAssign(x,exp) -> 
     let sym_env = Env.StringMap.add x exp st.sym_env in 
     let trace = Trace.Assign(x,exp)::st.trace in 
     [ { st with sym_env; trace } ]

and interp_cmd (st:state) (c:cmd) : state list = 
  match c with
  | Assign(x,exp) -> 
     let sym_env = Env.StringMap.add x exp st.sym_env in 
     let trace = Trace.Assign(x,exp)::st.trace in 
     [ { st with sym_env; trace } ]
  | Nop -> 
     [st]
  | Seq(c1,c2) -> 
     List.concat_map 
       (fun st1 -> interp_cmd st1 c2) 
       (interp_cmd st c1) 
  | If(e,c_tru, c_fls) -> 
     let e_tru = formula_of_exp st e in
     let st_tru = { st with path_cond = Smt.And(st.path_cond, e_tru) } in
     let e_fls = Smt.Not(e_tru) in 
     let st_fls = { st with path_cond = Smt.And(st.path_cond, e_fls) } in
     interp_cmd st_tru c_tru @ 
     interp_cmd st_fls c_fls
  | Apply(tbl) ->
     let _,acts = find_table tbl st.defns in
     List.concat_map (interp_action st) acts
  | Extr(x) ->
     let extract_cur = st.extract_cur + 1 in
     let input_slice = proj_input_pkt extract_cur in
     let sym_env = Env.StringMap.add x input_slice st.sym_env in
     let trace = Trace.Extract(x,input_slice)::st.trace in 
     [ { st with sym_env; extract_cur; trace } ]
  | Emit(x) -> 
     let emit_cur = st.emit_cur + 1 in
     let output_slice = Env.StringMap.find x st.sym_env in
     let old_output_pkt = Env.StringMap.find Smt.output_pkt st.sym_env in
     let old_output_typ = Env.StringMap.find Smt.output_pkt st.typ_env in 
     let sym_env = Env.StringMap.add Smt.output_pkt (mk_concat old_output_pkt output_slice) st.sym_env in
     let typ_env = Env.StringMap.add Smt.output_pkt (mk_concat_typ old_output_typ (Bit(8))) st.typ_env in
     let trace = Trace.Emit(x,output_slice)::st.trace in
     [ { st with sym_env; typ_env; emit_cur; trace } ]

let interp_defn (st:state) (d:defn) : state = 
  match d with 
  | VarDecl(typ,x,exp) ->
     let typ_env = Env.StringMap.add x typ st.typ_env in
     let sym_env = Env.StringMap.add x exp st.sym_env in
     let defns = d::st.defns in
     { st with typ_env; sym_env; defns }
  | Table _ -> 
     st

let add_env_constraints state = 
  let cond = Env.StringMap.fold (fun x e acc -> Smt.And(acc, Smt.Eq(Var(x), e))) state.sym_env state.path_cond in
  { state with path_cond = cond }

let add_output state = 
  { state with trace = Trace.Output(Var(Smt.output_pkt))::state.trace }

let interp_prog (p:prog) : state list = 
  let defns,main = p in 
  let st = List.fold_left interp_defn init_state defns in
  interp_cmd st main |> 
  List.map add_env_constraints |> 
  List.map add_output

let extract_model (st:state) (model:Smt.model) : exp Env.StringMap.t  =
  let go x acc = 
    let v = Smt.extract_value st.typ_env model x in
    Env.StringMap.add x v acc in
  Env.StringMap.fold (fun x _ acc -> go x acc) st.sym_env Env.StringMap.empty |> 
  go Smt.input_pkt |> 
  go Smt.output_pkt
