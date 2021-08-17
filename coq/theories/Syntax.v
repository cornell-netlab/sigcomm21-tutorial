Definition bitstring: Set := list bool.

Definition name: Set := nat.

Inductive uop: Set :=
| Hash
| Sum.

Inductive binop: Set :=
| Eq
| Neq.

Inductive expr: Set :=
| Var (x: name)
| NumLit (n: bitstring)
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

