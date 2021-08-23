Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Import List.ListNotations.

Set Implicit Arguments.
Section Env.
  Variable (K V: Type).
  Context `{K_eq_dec: EquivDec.EqDec K eq}.
  Definition t := list (K * V).
  Definition emp: t := [].
  Definition bind (k: K) (v: V) (e: t) : t :=
    (k, v) :: e.
  Fixpoint find (k: K) (e: t) : option V :=
    match e with
    | [] => None
    | (k', v) :: s =>
      if k == k'
      then Some v
      else find k s
    end.
End Env.
