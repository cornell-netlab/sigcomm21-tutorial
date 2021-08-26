module Interp = Coq_minip4.Interp
module Syntax = Coq_minip4.Syntax
module Util = Minip4.Util
module Smt = Minip4.Smt
module Trace = Minip4.Trace
module Printer = Minip4.Printer
module Vcgen = Minip4.Vcgen
module Symbex = Minip4.Symbex

let init_state = 
  let open Syntax in
  { store = [];
    in_pkt = [];
    out_pkt = [] }

let init_def_state = 
  let open Syntax in
  { type_env = []; tables = []; rules = [] }
  

let defns = 
  let open Syntax in 
  [VarDecl(Bit(8), "x", Bits (Util.repeat false 8))]

let cmd = 
  let open Syntax in 
  Seq(Extr("x"),
      If(Var("x"), 
         Seq(Assign("x", Bits([false;true;false;true;false;true;false;true])),
             Seq(Emit("x"),
                 Seq(Assign("x", Bits(Util.repeat true 8)),
                     Seq(Emit("x"), Emit("x"))))),
         Emit("x")))

let _ = ignore(cmd)

let cmd = 
  let open Syntax in 
  Seq(Extr("x"), Assert(Var("x")))

let prog = defns, cmd

let fuel = 100

let symbex () = 
  let states = Symbex.interp_prog prog in
  let go (state:Symbex.state) : unit = 
    Format.printf "\n====================\n";
    match Smt.check state.typ_env state.path_cond with 
    | None -> 
       ()
    | Some model -> 
       let bindings = Symbex.extract_model state model in
       let trace = List.rev_map (Trace.map_exp (fun e -> e |> Symbex.subst bindings |> Symbex.simplify)) state.trace in    
       List.iter (fun t -> Format.printf "%a\n" Pp.to_fmt (Trace.format_t t)) trace in 
  List.iter go states 

let interp () = 
   Format.printf "Initial Packet: %a\n%!" Pp.to_fmt (Printer.format_bitstring init_state.in_pkt);
   match Interp.interp_prog fuel init_def_state init_state prog with 
   | None -> 
     Format.printf "[Error]"
  | Some state -> 
     Format.printf "Final Packet: %a\n%!" Pp.to_fmt (Printer.format_bitstring state.out_pkt)

let vcgen () = 
  let state = Vcgen.vcgen_prog prog in
  match Smt.check state.typ_env (Smt.Not(state.cond)) with
  | None -> 
     Format.printf "Ok"
  | Some model -> 
     Format.printf "Precondition: %a\n" Pp.to_fmt (Smt.format_formula state.cond);
     Format.printf "Failed: {%s}\n" (Z3.Model.to_string model)
  
let () = 
   Format.printf "*** Welcome to MiniP4 ***\n%!";
   vcgen ()
