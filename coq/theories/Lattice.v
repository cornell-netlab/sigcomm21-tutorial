Require Import Coq.Relations.Relations.
Class Preorder (T: Type) : Type :=
  { le: relation T;
    le_refl: reflexive T le;
    le_trans: transitive T le }.
Notation "x <= y" := (le x y).
(* This is a "typeclassification" of the compcert Lattice library. *)
Class Semilattice (T: Type) `{Preorder T} : Type :=
  { bot: T;
    bot_le: forall x, bot <= x;
    lub: T -> T -> T;
    lub_left: forall x y, le x (lub x y);
    lub_right: forall x y, le y (lub x y); }.