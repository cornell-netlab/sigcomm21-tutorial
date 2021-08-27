Require Import MiniP4.Syntax.

Open Scope string_scope.
Open Scope list_scope.

Definition meta_t : typ :=
  (* drop flag, port number *)
  Prod Bool (Bit 1).

Definition ipv4_t : typ :=
  (* src addr, dst addr *)
  Prod (Bit 8) (Bit 8).

Definition zeros (n: nat) : exp :=
  Bits (List.repeat false n).

Definition set_out0 : action :=
  ActAssign "meta" (Tuple (EBool false) (Bits [false])).

Definition set_out1 : action :=
  ActAssign "meta" (Tuple (EBool false) (Bits [true])).

Definition act_drop : action :=
  ActAssign "meta" (Tuple (EBool true) (Proj2 (Var "meta"))).

Definition acl_defns : list defn :=
  [VarDecl meta_t "meta" (Tuple (EBool false) (Bits [false]));
   VarDecl ipv4_t "ip" (Tuple (zeros 8) (zeros 8));
   Table "route" (Proj1 (Var "ip")) [set_out0; set_out1];
   Table "acl" (Var "ip") [act_drop; ActNop]].

Definition acl_cmd : cmd :=
  Seq (Extr "ip")
      (Seq (Apply "route")
           (Seq (Apply "acl")
                (Emit "ip"))).

Definition acl: prog :=
  (acl_defns, acl_cmd).

Eval compute in acl.
