Require Import Coq.Classes.EquivDec.
Require Import PeanoNat.
Require MiniP4.Env.
Definition bitstring: Set := list bool.

Definition name: Set := nat.
Instance name_eq_dec: EqDec name eq := Nat.eq_dec.

Inductive uop: Set :=
| Hash
| Sum.

Inductive binop: Set :=
| Eq
| Neq.

Inductive exp: Set :=
| Var (x: name)
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
| Call (a: name).

Inductive typ: Set :=
| Bit (n: nat)
| Bool
| Prod (ts: list typ).

Inductive defn: Set :=
| VarDecl (t: typ) (x: name) (e: exp)
| Action (a: name) (c: cmd)
| Table (t: name) (keys: exp) (actions: list name).

Definition prog: Set :=
  list defn * cmd.

Inductive val: Set :=
| VBits (bs: bitstring)
| VBool (b: bool)
| VTuple (vs: list val).

Record action :=
  { body: cmd }.

Record rule :=
  { rule_match: exp;
    rule_action: name }.

Record table :=
  { table_key: exp;
    table_acts: list name; }.

Record state :=
  { store: Env.t name val;
    type_env: Env.t name typ;
    pkt: list bool;
    acts: Env.t name action;
    tables: Env.t name (table * list rule) }.
