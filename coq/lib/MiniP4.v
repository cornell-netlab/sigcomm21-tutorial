Definition bitstring := list bool.

Inductive binop :=
| Eq
| Add
| Sub.

Inductive expr :=
| NumLit (n: bitstring)
| BinOp (o: binop) (e1 e2: expr).
