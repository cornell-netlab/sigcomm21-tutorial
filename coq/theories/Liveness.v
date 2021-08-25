Require Import Coq.Lists.List.
Require Import MiniP4.Syntax.
Require MiniP4.Env.
Open Scope string_scope.
Open Scope list_scope.

Definition varset := list name.

Definition emp : varset := [].

Definition mk_varset (vs: list name) :=
  nodup name_eq_dec vs.

Definition check (x: name) (s: varset) : bool :=
  if In_dec name_eq_dec x s then true else false.

Definition add (x: name) (s: varset) : varset :=
  if check x s then s else x :: s.

Definition drop (x: name) (s: varset) : varset :=
  List.remove name_eq_dec x s.

Definition union (v1 v2: varset) : varset :=
  List.fold_left (fun u x => add x u) v2 v1.

Definition union_all (vs: list varset) : varset :=
  List.fold_left union vs emp.

Fixpoint fv (e: exp) : varset :=
 match e with
 | Var x => mk_varset [x]
 | EBool b => emp
 | Bits bs => emp
 | Tuple exps => union_all (List.map fv exps)
 | Proj e n => fv e
 | BinOp o e1 e2 => union (fv e1) (fv e2)
 | UOp o e => fv e
 end.

Import ListNotations.
Eval compute in (List.fold_right (fun x l => l ++ [x]) [] [1;2;3]).

Fixpoint act_live (live: varset) (act: action) : varset :=
  match act with
  | ActAssign x e => 
    union (drop x live) (fv e)
  | ActSeq a1 a2 =>
    act_live (act_live live a2) a1
  | ActNop => live
  end.

Definition acts_live (live: varset) (acts: list action) : varset :=
  union_all (List.map (act_live live) acts).

Fixpoint dead_store_elim
         (tables: Env.t name table)
         (live: varset)
         (c: cmd) : varset * cmd :=
  match c with
  | Assign x e =>
    if check x live
    then (union (drop x live) (fv e), c)
    else (live, Nop)
  | Nop =>
    (live, Nop)
  | Seq c1 c2 =>
    let (live, c2) := dead_store_elim tables live c2 in
    let (live, c1) := dead_store_elim tables live c1 in
    (live, Seq c1 c2)
  | If e c1 c2 =>
    let (live1, c1) := dead_store_elim tables live c1 in
    let (live2, c2) := dead_store_elim tables live c2 in
    (union_all [fv e; live1; live2], If e c1 c2)
  | Extr x =>
    (drop x live, c)
  | Emit x =>
    (add x live, c)
  | Apply t =>
    match Env.find t tables with
    | Some t =>
      let live := acts_live live t.(table_acts) in
      (union (fv (t.(table_key))) live, c)
    | None => (live, c)
    end
  end.

Eval compute in dead_store_elim [] [] (Assign "x" (Bits [true])).
Eval compute in dead_store_elim [] [] (Seq (Assign "x" (Bits [true])) (Assign "x" (Var "x"))).
Eval compute in dead_store_elim [] ["x"; "y"] (Seq (Assign "x" (Bits [true])) (Assign "x" (Var "x"))).
Eval compute in dead_store_elim [] ["x"; "y"] (Seq (Assign "x" (Bits [true])) (Assign "x" (Var "y"))).
