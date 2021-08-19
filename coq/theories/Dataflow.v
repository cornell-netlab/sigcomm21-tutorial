Require Import MiniP4.Lattice.
Require Import MiniP4.Syntax.
Section Dataflow.
  Variable (T: Type).
  Context `{L: Lattice.Semilattice T}.
  Variable transfer: cmd -> T -> T.
  Definition fix_cmd (c: cmd) (x: T) := x.
End Dataflow.
