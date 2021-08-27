Require Import MiniP4.Syntax.

Open Scope string_scope.
Open Scope list_scope.

Definition meta_t : typ :=
  (* drop flag, port number *)
  Prod Bool (Bit 1).

Definition addr_t : typ :=
  Bit 8.

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
   VarDecl addr_t "src" (zeros 8);
   VarDecl addr_t "dst" (zeros 8);
   Table "route" (Var "dst") [set_out0; set_out1];
   Table "acl" (Tuple (Var "src") (Var "dst")) [act_drop; ActNop]].

Definition acl_cmd : cmd :=
  Seq (Extr "src")
      (Seq (Extr "dst")
           (Seq (Apply "route")
                (Seq (Apply "acl")
                     (Seq (Emit "src")
                          (Emit "dst"))))).

Definition acl: prog :=
  (acl_defns, acl_cmd).
  
Eval compute in acl.
