Require Import MiniP4.Syntax.

Open Scope string_scope.

Definition meta_t : typ :=
  (* drop flag, port number *)
  Prod [Bool; Bit 8].

Definition ipv4_t : typ :=
  (* src addr, dst addr *)
  Prod [Bit 8; Bit 8].

Definition zeros (n: nat) : exp :=
  Bits (List.repeat false n).

Definition ipv4_defns : list defn :=
  [VarDecl ipv4_t "ip" (Tuple [zeros 8; zeros 8]);
   Action "set_out"
          [("port", Bit 8)]
          (Assign "meta" (Tuple [EBool false; Var "port"]));
   Table "route" (Proj (Var "ip") 1) ["set_out"]].

Definition ipv4_cmd : cmd :=
  Block [Extr "ip";
         Apply "route";
         Emit "ip"].
