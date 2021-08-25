open Coq_minip4
open Minip4
open Syntax
open Interp

let init_def_state = 
  { type_env = [];
    tables = [];
    rules = []; }

let init_state = 
  { store = [];
    pkt = [] }

let defns = []

let cmd = Nop

let prog = defns, cmd

let fuel = 100

let () = 
   Format.printf "*** Welcome to MiniP4 ***\n%!";
   Format.printf "Initial Packet: %a\n%!" Pp.to_fmt (Printer.format_bitstring init_state.pkt);
   match interp_prog fuel init_def_state init_state prog with 
   | None -> 
     Format.printf "[Error]"
   | Some state -> 
     Format.printf "Final Packet: %a\n%!" Pp.to_fmt (Printer.format_bitstring state.pkt)
