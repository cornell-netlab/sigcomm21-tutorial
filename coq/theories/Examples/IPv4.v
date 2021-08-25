Require Import MiniP4.Syntax.

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
  ActAssign "meta" (Tuple (EBool false) (Proj1 (Var "ip"))).

Definition ipv4_defns : list defn :=
  [VarDecl ipv4_t "ip" (Tuple (zeros 8) (zeros 8));
   Table "route" (Proj1 (Var "ip")) [set_out]].

Definition ipv4_cmd : cmd :=
  Seq (Extr "ip")
      (Seq (Apply "route")
           (Emit "ip")).
