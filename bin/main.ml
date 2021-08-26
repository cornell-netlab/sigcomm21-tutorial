open Coq_minip4.Syntax
open Minip4

let init_state = 
  { store = [];
    type_env = [];
    pkt = [];
    acts = [];
    tables = []; }

let defns = [VarDecl(Bit(8), "x", Bits (Util.repeat false 8))]

let cmd = Block 
            [ Extr("x");
              If(Var("x"), 
                 Block[ Assign("x", Bits([false;true;false;true;false;true;false;true]));
                        Emit("x");
                        Assign("x", Bits(Util.repeat true 8));
                        Emit("x")],
                 Block[ Emit("x") ]) ]

let prog = defns,cmd

let fuel = 100

let symbex () = 
  let () = Format.printf "*** Welcome to MiniP4 ***%!" in
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
  Format.printf "*** Welcome to MiniP4 ***\n%!";
  Format.printf "Initial Packet: %a\n%!" Pp.to_fmt (Printer.format_bitstring init_state.pkt);
  match Coq_minip4.Interp.interp_prog fuel init_state prog with 
  | None -> 
     Format.printf "[Error]"
  | Some state -> 
     Format.printf "Final Packet: %a\n%!" Pp.to_fmt (Printer.format_bitstring state.pkt)

let () = symbex ()
