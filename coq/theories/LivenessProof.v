Require Import Coq.Lists.List.
Require Import MiniP4.Syntax.
Require MiniP4.Env.
Require Import MiniP4.Liveness.
Require Import MiniP4.Interp.
Open Scope string_scope.
Open Scope list_scope.

Definition dead (x: name) (c: cmd) : Prop :=
  forall n s c s',
    interp_cmd n s c = Some s' ->
    forall v,
      exists m,
        interp_cmd m (assign s x v) = Some s'.
