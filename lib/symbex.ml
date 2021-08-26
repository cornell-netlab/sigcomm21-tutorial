open Coq_minip4.Syntax

type state = 
  { defns: defn list;
    typ_env : typ Env.StringMap.t;
    sym_env : exp Env.StringMap.t;
    extract_cur : int;
    emit_cur : int;
    path_cond : Smt.formula;
    trace : Trace.t list }

let mtu = 4

let init_typ_env = 
  let pkt_typ = Prod(Util.repeat (Bit(8)) mtu) in
  let bindings = 
    [ (Smt.input_pkt, pkt_typ);
      (Smt.output_pkt, Prod([])) ] in
  Env.StringMap.of_seq (List.to_seq bindings)

let init_state = 
  { defns = [];
    typ_env = init_typ_env;
    sym_env = Env.StringMap.empty;
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
  | Tuple(es) -> Tuple(List.map (subst env) es)
  | Proj(e,n) -> Proj(subst env e, n)
  | BinOp(o,e1,e2) -> BinOp(o,subst env e1, subst env e2)
  | UOp(o,e) -> UOp(o,subst env e)

let rec simplify (e:exp) : exp = 
  match e with 
  | Var _ -> e
  | EBool _ -> e
  | Bits _ -> e
  | Tuple(es) -> Tuple(List.map simplify es)
  | Proj(Tuple(es),n) -> simplify (List.nth es (n-1))
  | Proj(e,n) -> Proj(simplify e, n)
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

let rec find_action act defns = 
  match defns with 
  | [] -> 
     failwith "Unexpected error: could not find action" 
  | Action(act',params,body)::defns' -> 
     if act = act' then
       (params, body)
     else 
       find_action act defns'
  | _::defns' -> 
     find_action act defns'

let rec interp_action (st:state) (act:name) : state list = 
  let _,body = find_action act st.defns in 
  interp_cmd st body

and interp_cmd (st:state) (c:cmd) : state list = 
  match c with
  | Assign(x,e) -> 
     let sym_env = Env.StringMap.add x e st.sym_env in 
     let trace = Trace.Assign(x,e)::st.trace in 
     [ { st with sym_env; trace } ]
  | Block(cs) -> 
     let rec loop acc cs = 
       match cs with 
       | [] -> acc
       | c::cs' -> 
          let acc' = List.concat_map (fun st -> interp_cmd st c) acc in 
          loop acc' cs' in 
     loop [st] cs
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
     let input_slice = Proj(Var(Smt.input_pkt), extract_cur) in
     let sym_env = Env.StringMap.add x input_slice st.sym_env in
     let trace = Trace.Extract(x,input_slice)::st.trace in 
     [ { st with sym_env; extract_cur; trace } ]
  | Emit(x) -> 
     let emit_cur = st.emit_cur + 1 in
     let output_slice = Env.StringMap.find x st.sym_env in
     let old_output_pkt = 
       try 
         match Env.StringMap.find Smt.output_pkt st.sym_env with 
         | Tuple(es) -> es
         | _ -> failwith "Unexpected error: output packet is not a tuple"
       with Not_found -> 
         [] in
     let old_output_typ = 
       match Env.StringMap.find Smt.output_pkt st.typ_env with 
       | Prod(ts) -> ts
       | _ -> failwith "Unexpected error: type of output packet is not a product" in     
     let sym_env = Env.StringMap.add Smt.output_pkt (Tuple(old_output_pkt @ [output_slice])) st.sym_env in
     let typ_env = Env.StringMap.add Smt.output_pkt (Prod(old_output_typ @ [Bit(8)])) st.typ_env in
     let trace = Trace.Emit(x,output_slice)::st.trace in
     [ { st with sym_env; typ_env; emit_cur; trace } ]
  | Call(act,args) -> 
     let params,body = find_action act st.defns in
     let typ_env, sym_env = 
       List.fold_left (fun (tenv,senv) ((x,typ),arg) -> 
           (Env.StringMap.add x typ tenv,
            Env.StringMap.add x arg senv))
         (st.typ_env, st.sym_env)
         (List.combine params args) in 
     let st = { st with typ_env; sym_env } in
     interp_cmd st body

let interp_defn (st:state) (d:defn) : state = 
  match d with 
  | VarDecl(typ,x,exp) ->
     let typ_env = Env.StringMap.add x typ st.typ_env in
     let sym_env = Env.StringMap.add x exp st.sym_env in
     let defns = d::st.defns in
     { st with typ_env; sym_env; defns }
  | Table _ -> 
     st
  | Action _ -> 
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
