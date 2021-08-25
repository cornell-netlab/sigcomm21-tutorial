Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import MiniP4.Syntax.
Require MiniP4.Env.
Require Import MiniP4.Liveness.
Require Import MiniP4.Interp.
Open Scope string_scope.
Open Scope list_scope.

Lemma check_union_false:
  forall x a b,
    check x (union a b) = false ->
    check x a = false /\ check x b = false.
Proof.
Admitted.

Definition dead (x: name) (c: cmd) : Prop :=
  forall n s s',
    interp_cmd n s c = Some s' ->
    forall v,
      exists m,
        interp_cmd m (assign s x v) c = Some s'.

Lemma exp_assign_fv:
  forall s e x v,
    check x (fv e) = false ->
    interp_exp (assign s x v) e = interp_exp s e.
Proof.
  induction e.
  simpl.
Admitted.

Lemma option_map_Some:
  forall A B (f: A -> B) x y,
    option_map f x = Some y ->
    exists z,
      x = Some z /\ y = f z.
Proof.
  unfold option_map.
  intros.
  destruct x.
  - eexists.
    intuition congruence.
  - congruence.
Qed.

Lemma assign_overwrite:
  forall s x v v',
    assign (assign s x v) x v' = assign s x v'.
Proof.
  intros.
  unfold assign, set_store; simpl.
  rewrite Env.bind_overwrite.
  tauto.
Qed.

Lemma check_cons_neq:
  forall x y s,
    x <> y ->
    check x (y :: s) = check x s.
Proof.
  intros.
  unfold check.
  repeat destruct (in_dec _ _ _); try tauto.
  - simpl in *.
    intuition congruence.
  - simpl in *.
    tauto.
Qed.

Lemma check_cons_eq:
  forall x s,
    check x (x :: s) = true.
Proof.
  intros.
  unfold check.
  destruct (in_dec _ _ _); simpl in *; tauto.
Qed.

Lemma check_drop:
  forall x y s,
    x <> y ->
    check x (drop y s) = check x s.
Proof.
  induction s; simpl; intros.
  - reflexivity.
  - unfold drop.
    destruct (name_eq_dec y a), (name_eq_dec x a).
    + congruence.
    + rewrite check_cons_neq; auto.
    + cbv in e; subst.
      now rewrite !check_cons_eq.
    + rewrite !check_cons_neq; auto.
Qed.

Lemma check_emp:
  forall a,
    check a emp = false.
Proof.
  unfold emp.
  intros.
  reflexivity.
Qed.

Lemma check_add_eq:
  forall x s,
    check x (add x s) = true.
Proof.
  intros.
  unfold add.
  destruct (check x s) eqn:?; [tauto|].
  apply check_cons_eq.
Qed.

Lemma check_add_neq:
  forall x y s,
    x <> y ->
    check x (add y s) = check x s.
Proof.
  intros.
  unfold add.
  destruct (check y s) eqn:?; [tauto|].
  apply check_cons_neq.
  tauto.
Qed.

Lemma union_emp_l:
  forall s,
    union emp s = s.
Proof.
  (* Not actually true, needs hypothesis about duplicates in s *)
Admitted.

Lemma interp_cmd_fuel:
  forall m n s c v,
    m >= n ->
    interp_cmd n s c = Some v ->
    interp_cmd m s c = Some v.
Proof.
Admitted.

Lemma interp_extr_assign:
  forall s x v t,
    interp_extr (assign s x v) x t = interp_extr s x t.
Proof.
  intros.
  unfold interp_extr.
  simpl.
  destruct (extr (pkt s) t) as [[? ?]|].
  - rewrite Env.bind_overwrite.
    reflexivity.
  - reflexivity.
Qed.

Lemma dse_dead:
  forall tables live c live' c',
    dead_store_elim tables live c = (live', c') ->
    forall x,
      check x live' = false ->
      dead x c \/ check x live = false.
Proof.
  induction c; simpl; intros.
  - destruct (name_eq_dec x x0); unfold Equivalence.equiv in *; subst.
    + destruct (check x0 live) eqn:?; inversion H; subst.
      * apply check_union_false in H0; intuition.
        left.
        unfold dead; intros.
        exists n.
        destruct n; simpl in *; auto.
        rewrite exp_assign_fv by auto.
        eapply option_map_Some in H0.
        destruct H0 as [z [? ?]].
        subst.
        rewrite H0.
        simpl.
        rewrite assign_overwrite.
        reflexivity.
      * tauto.
    + right.
      destruct (check x live) eqn:?; simpl in *.
      * inversion H.
        subst.
        apply check_union_false in H0.
        destruct H0 as [? ?].
        rewrite check_drop in H0; eauto.
      * congruence.
  - admit.
  - destruct (dead_store_elim tables live c1) as [live1 c1'] eqn:?.
    destruct (dead_store_elim tables live c2) as [live2 c2'] eqn:?.
    unfold union_all in *.
    simpl in H.
    inversion H; clear H.
    subst live'.
    subst c'.
    specialize (IHc1 live1 c1' eq_refl x).
    specialize (IHc2 live2 c2' eq_refl x).
    apply check_union_false in H0.
    destruct H0.
    apply check_union_false in H.
    destruct H.
    apply IHc1 in H1.
    apply IHc2 in H0.
    intuition.
    left.
    rewrite union_emp_l in H.
    unfold dead; intros.
    destruct n; simpl in *; try congruence.
    destruct (interp_exp s e) eqn:?; try congruence.
    destruct (val_eq_dec v0 (VBits [true])) as [e0 | e0]; cbv in e0; subst.
    * apply H2 in H0.
      destruct (H0 v) as [m ?].
      exists (S m).
      destruct m; [cbn in *; congruence|].
      remember (S m) as m'.
      simpl.
      rewrite exp_assign_fv; auto.
      rewrite Heqo.
      rewrite Heqm'.
      eapply interp_cmd_fuel; [|eassumption].
      lia.
    * assert (interp_cmd n s c2 = Some s').
      {
        destruct v0; try congruence.
        destruct bs as [|[|] [|?]]; try congruence.
      }
      clear H0.
      apply H1 in H3.
      destruct (H3 v) as [m ?].
      exists (S m).
      destruct m; [cbn in *; congruence|].
      remember (S m) as m'.
      simpl.
      rewrite exp_assign_fv; auto.
      rewrite Heqo.
      cut (interp_cmd m' (assign s x v) c2 = Some s').
      {
        destruct v0; try congruence.
        destruct bs as [|[|] [|?]]; try congruence.
      }
      rewrite Heqm'.
      eapply interp_cmd_fuel; [|eassumption].
      lia.
  - inversion H.
    subst.
    clear H.
    destruct (name_eq_dec x x0).
    + cbv in e; subst x0.
      left.
      unfold dead; intros.
      exists n.
      destruct n; simpl in *; try congruence.
      destruct (Env.find x (type_env s)) in *; try congruence.
      rewrite interp_extr_assign.
      tauto.
    + right.
      rewrite check_drop in H0; congruence.
  - right.
    destruct (name_eq_dec x x0).
    + cbv in e; subst x0.
      inversion H.
      subst live'.
      rewrite check_add_eq in *.
      congruence.
    + inversion H; subst live'.
      rewrite check_add_neq in H0; eauto.
  - admit.
  - admit.
Admitted.
