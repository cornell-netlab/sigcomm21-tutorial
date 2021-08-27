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

val format_formula : formula -> 'a Pp.t

val subst_formula : name -> term -> formula -> formula

val formula_of_exp : typ -> exp -> formula

val input_pkt : name
val cursor: name
val output_pkt : name
val mtu : int
val init_typ_env : typ Env.StringMap.t

type model = Z3.Model.model

val extract_value : typ Env.StringMap.t -> model -> name -> exp
val check : typ Env.StringMap.t -> formula -> model option
