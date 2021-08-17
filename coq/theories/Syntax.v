Require Import Coq.Lists.List.
Import List.ListNotations.

Definition bitstring: Set := list bool.

Definition name: Set := nat.
Definition name_eq_dec: forall x y: nat, {x = y} + {x <> y} := PeanoNat.Nat.eq_dec.

Inductive uop: Set :=
| Hash
| Sum.

Inductive binop: Set :=
| Eq
| Neq.

Inductive expr: Set :=
| Var (x: name)
| Bits (bs: bitstring)
| Tuple (exps: list expr)
| Proj (e: expr) (n: nat)
| BinOp (o: binop) (e1 e2: expr)
| UOp (o: uop) (e: expr).

Inductive cmd: Set :=
| Assign (x: name) (e: expr)
| Block (cs: list cmd)
| If (e: expr) (c1 c2: cmd)
| Extr (x: name)
| Emit (x: name)
| Apply (t: name)
| Call (a: name).

Inductive typ: Set :=
| Bit (n: nat)
| Bool
| Prod (ts: list typ).

Inductive defn: Set :=
| VarDecl (t: typ) (x: name) (e: expr)
| Action (a: name) (c: cmd)
| Table (t: name) (keys: expr) (actions: list name).

Definition prog: Set :=
  list defn * cmd.

Inductive val: Set :=
| VBits (bs: bitstring)
| VTuple (vs: list val).

Definition store := list (name * val).
Definition emp: store := nil.
Definition bind (n: name) (v: val) (s: store) : store :=
  (n, v) :: s.
Fixpoint find (n: name) (s: store) : option val :=
  match s with
  | [] => None
  | (k, v) :: s =>
    if name_eq_dec n k
    then Some v
    else find n s
  end.
