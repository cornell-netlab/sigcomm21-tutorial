open Coq_minip4.Syntax
open Smt

let mk_implies p q = Or(Not(p), q)

type state = 
  { defns : defn list;
    typ_env : typ Env.t; 
    cond : formula }

let init_state = 
  { defns = [];
    typ_env = Smt.init_typ_env;
    cond = True }

let rec vcgen_act (st:state) (act:action) : state = 
  match act with 
  | ActNop -> st
  | ActSeq(a1,a2) -> 
     vcgen_act (vcgen_act st a2) a1
  | ActAssign(x,e) -> 
     let cond = Smt.subst_formula x e st.cond in 
     { st with cond }

let rec vcgen_cmd (st:state) (c:cmd) : state = 
  match c with 
  | Nop -> 
     st
  | Seq(c1,c2) ->
     vcgen_cmd (vcgen_cmd st c2) c1
  | Assign(x,e) -> 
     let cond = Smt.subst_formula x e st.cond in
     { st with cond }
  | If(e,c1,c2) -> 
     let typ = Check.typ_of_exp st.typ_env e in
     let e_tru = formula_of_exp typ e in 
     let e_fls = Not(e_tru) in 
     let cond = 
       And(mk_implies e_tru (vcgen_cmd st c1).cond, 
           mk_implies e_fls (vcgen_cmd st c2).cond) in
     { st with cond }
  | Extr(x) -> 
     let cmd = 
       Seq(Assign(x,Proj1(Var(Smt.input_pkt))),
           Assign(Smt.input_pkt, Proj2(Var(Smt.input_pkt)))) in
     vcgen_cmd st cmd
  | Emit(x) -> 
     let cmd = Assign(Smt.output_pkt, Tuple(Var(Smt.output_pkt), Var(x))) in 
     vcgen_cmd st cmd
  | Apply(t) ->
     let _,acts = Symbex.find_table t st.defns in
     let sts = List.map (vcgen_act st) acts in
     let cond = List.fold_left (fun acc st -> Or(acc,st.cond)) False sts in 
     { st with cond }
  | Assert(e) -> 
     let typ = Check.typ_of_exp st.typ_env e in
     let e_tru = formula_of_exp typ e in 
     let cond = And(e_tru, st.cond) in 
     { st with cond }
  | Assume(e) -> 
     let typ = Check.typ_of_exp st.typ_env e in
     let e_tru = formula_of_exp typ e in 
     let cond = mk_implies e_tru st.cond in 
     { st with cond }

let vcgen_defn st d = 
  match d with 
  | VarDecl(typ,x,_) ->
     let typ_env = Env.StringMap.add x typ st.typ_env in 
     let defns = st.defns @ [d] in
     { st with defns; typ_env }
  | Table _ -> 
     let defns = st.defns @ [d] in
     { st with defns }

let vcgen_prog p = 
  let defns,main = p in 
  let st = List.fold_left vcgen_defn init_state defns in
  vcgen_cmd st main
