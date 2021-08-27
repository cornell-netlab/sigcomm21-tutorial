Require Import MiniP4.Syntax.
Require Import MiniP4.Liveness.

Open Scope string_scope.

Definition meta_t : typ :=
  (* drop flag, port number *)
  Prod Bool (Bit 8).

Definition ipv4_t : typ :=
  (* src addr, dst addr *)
  Prod (Bit 8) (Bit 8).

Definition zeros (n: nat) : exp :=
  Bits (List.repeat false n).

Definition set_out : action :=
  ActAssign "meta" (Tuple (EBool false) (Proj2 (Var "ip"))).

Definition act_drop : action :=
  ActAssign "meta" (Tuple (EBool true) (Proj2 (Var "meta"))).

Definition ipv4_defns : list defn :=
  [VarDecl ipv4_t "ip" (Tuple (zeros 8) (zeros 8));
   Table "route" (Proj1 (Var "ip")) [set_out];
   Table "acl" (Var "ip") [act_drop; ActNop]].

Definition acl_cmd : cmd :=
  Seq (Extr "ip")
      (Seq (Apply "route")
           (Seq (Apply "acl")
                (Emit "ip"))).

Definition tables: Env.t name Syntax.table :=
  [("route", {| table_key := (Proj1 (Var "ip")); table_acts := [set_out] |});
   ("acl", {| table_key := (Var "ip"); table_acts := [act_drop; ActNop] |})].

Eval compute in (dead_store_elim tables emp acl_cmd).
