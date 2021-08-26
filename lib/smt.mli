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

val input_pkt : name
val output_pkt : name

type model

val extract_value : typ Env.StringMap.t -> model -> name -> exp
val check : typ Env.StringMap.t -> formula -> model option
