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
| Tuple (exps: list exp)
| Proj (e: exp) (n: nat)
| BinOp (o: binop) (e1 e2: exp)
| UOp (o: uop) (e: exp).

Inductive cmd: Set :=
| Assign (x: name) (e: exp)
| Block (cs: list cmd)
| If (e: exp) (c1 c2: cmd)
| Extr (x: name)
| Emit (x: name)
| Apply (t: name)
| Call (a: name) (args: list exp).

Inductive typ: Set :=
| Bit (n: nat)
| Bool
| Prod (ts: list typ).

Inductive defn: Set :=
| VarDecl (t: typ) (x: name) (e: exp)
| Action (a: name) (params: list (name * typ)) (c: cmd)
| Table (t: name) (keys: exp) (actions: list name).

Definition prog: Set :=
  list defn * cmd.

Inductive val: Set :=
| VBits (bs: bitstring)
| VBool (b: bool)
| VTuple (vs: list val).

Record action :=
  { params: list (name * typ);
    body: cmd }.

Record rule :=
  { rule_match: exp;
    rule_action: name;
    rule_args: list val }.

Record table :=
  { table_key: exp;
    table_acts: list name; }.

Record state :=
  { store: Env.t name val;
    type_env: Env.t name typ;
    pkt: list bool;
    acts: Env.t name action;
    tables: Env.t name table;
    rules: Env.t name (list rule) }.
