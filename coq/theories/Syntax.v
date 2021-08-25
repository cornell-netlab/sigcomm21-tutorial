Require Import Coq.Classes.EquivDec.
Require Export Coq.Strings.String.
Require Import PeanoNat.
Require MiniP4.Env.
Require Import Coq.Lists.List.
Export ListNotations.
Definition bitstring: Set := list bool.

Definition name: Set := string.
Instance name_eq_dec: EqDec name eq := string_dec.

Inductive uop: Set :=
| Hash
| Sum.

Inductive binop: Set :=
| Eq
| Neq.

Inductive exp: Set :=
| Var (x: name)
| EBool (b: bool)
| Bits (bs: bitstring)
| Tuple (exp1 exp2: exp)
| Tt (* unit *)
| Proj1 (e: exp)
| Proj2 (e: exp)
| BinOp (o: binop) (e1 e2: exp)
| UOp (o: uop) (e: exp).

Inductive cmd: Set :=
| Assign (x: name) (e: exp)
| Nop
| Seq (c1 c2: cmd)
| If (e: exp) (c1 c2: cmd)
| Extr (x: name)
| Emit (x: name)
| Apply (t: name).

Inductive typ: Set :=
| Bit (n: nat)
| Bool
| Unit
| Prod (t1 t2: typ).

Inductive action :=
| ActAssign (x: name) (e: exp)
| ActSeq (a1 a2: action)
| ActNop.

Inductive defn: Set :=
| VarDecl (t: typ) (x: name) (e: exp)
| Table (t: name) (keys: exp) (acts: list action).

Definition prog: Set :=
  list defn * cmd.

Inductive val: Set :=
| VBits (bs: bitstring)
| VBool (b: bool)
| VUnit
| VPair (v1 v2: val).

Record rule :=
  { rule_match: exp;
    rule_action: nat }.

Record table :=
  { table_key: exp; table_acts: list action }.

Record def_state :=
  { type_env: Env.t name typ;
    tables: Env.t name table;
    rules: Env.t name (list rule) }.

Record state :=
  { store: Env.t name val;
    pkt: list bool }.
