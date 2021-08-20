Require Import Coq.Lists.List.
Require Import MiniP4.Syntax.
Require MiniP4.Env.

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

(* Backwards computation of live vars before c given vars in [live]
are all live after c *)
Fixpoint live_vars_transf
         (tables: Env.t name table)
         (live: varset)
         (c: cmd) : varset :=
  match c with
  | Assign x e =>
    union (drop x live) (fv e)
  | Block cs =>
    List.fold_right
      (fun c live =>
         live_vars_transf tables live c)
      live
      cs
  | If e c1 c2 =>
    union_all [fv e;
               live_vars_transf tables live c1;
               live_vars_transf tables live c2]
  | Extr x =>
    drop x live
  | Emit x =>
    add x live
  | Apply t =>
    match Env.find t tables with
    | Some t => union (fv (t.(table_key))) live
    | None => live
    end
  | Call a params =>
    union (union_all (List.map fv params)) live
  end.

Fixpoint dead_store_elim
         (tables: Env.t name table)
         (live: varset)
         (c: cmd) : varset * cmd :=
  match c with
  | Assign x e =>
    if check x live
    then (union (drop x live) (fv e), c)
    else (live, Block [])
  | Block cs =>
    let (live, cs) :=
        List.fold_right
          (fun c '(live, cs) =>
             let (live, c') := dead_store_elim tables live c in
             match c' with
             | Block [] =>
               (live, cs)
             | c' =>
               (live, c' :: cs)
             end)
          (live, [])
          cs
    in
    (live, Block cs)
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
    | Some t => (union (fv (t.(table_key))) live, c)
    | None => (live, c)
    end
  | Call a params =>
    (union (union_all (List.map fv params)) live, c)
  end.
