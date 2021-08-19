Require Import MiniP4.Syntax.
Require MiniP4.Env.

Definition varset := Env.t name bool.
Definition emp : varset := Env.emp _ _.
Definition add (x: name) (s: varset) : varset := Env.bind x true s.
Definition check (x: name) (s: varset) : bool :=
  match Env.find x s with
  | Some b => b
  | None => false
  end.
Definition drop (x: name) (s: varset) : varset := Env.bind x false s.

Fixpoint fv' (v: varset) (e: exp) : varset :=
 match e with
 | Var x => add x v
 | Bits bs => v
 | Tuple exps => List.fold_left (fun v e => fv' v e) exps v
 | Proj e n => fv' v e
 | BinOp o e1 e2 => fv' (fv' v e1) e2
 | UOp o e => fv' v e
 end.

Definition fv (e: exp) : varset :=
  fv' emp e.

Definition live_vars (c: cmd) :=
  match c with
  | Assign x e => fv e
  | Block cs => emp
  | If e c1 c2 => emp
  | Extr x => emp
  | Emit x => emp
  | Apply t => emp
  | Call a => emp
  end.
