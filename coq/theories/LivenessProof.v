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

Definition agree (s: varset) (s1 s2: Env.t name val) : Prop :=
  Forall (fun x => Env.find x s1 = Env.find x s2) s.

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
  forall m n ds s c v,
    m >= n ->
    interp_cmd n ds s c = Some v ->
    interp_cmd m ds s c = Some v.
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

Lemma agree_refl:
  forall v s,
    agree v s s.
Proof.
  unfold agree.
  intros.
  rewrite Forall_forall.
  intros.
  reflexivity.
Qed.

Lemma agree_bind_neq:
  forall x live v s,
  check x live = false ->
  agree live (Env.bind x v s) s.
Proof.
  intros.
  unfold agree.
  apply Forall_forall.
  intros.
  unfold check in H.
  destruct (in_dec name_eq_dec x live); try congruence.
  rewrite Env.find_bind_neq; eauto.
  intro; subst; tauto.
Qed.

Lemma dse_corr:
  forall c live live' c' ds,
    dead_store_elim ds.(tables) live c = (live', c') ->
    forall n s1 s1',
      interp_cmd n ds s1 c = Some s1' ->
      forall s2,
        agree live' s1.(store) s2.(store) ->
        s1.(pkt) = s2.(pkt) ->
        exists s2',
          interp_cmd n ds s2 c' = Some s2' /\
          agree live s1'.(store) s2'.(store) /\
          s1'.(pkt) = s2'.(pkt).
Proof.
  induction c; simpl; intros.
  - destruct n; simpl in * |-; try congruence.
    destruct (check x live) eqn:?; inversion H; clear H; subst.
    + simpl.
      admit.
    + admit.
  - admit.
  - destruct n; try solve [simpl in H0; congruence].
    simpl in H0.
    destruct (interp_cmd n ds s1 c1) eqn:?;
             [|destruct n; try congruence].
    destruct (dead_store_elim (tables ds) live c2) as [live2 c2'] eqn:?.
    destruct (dead_store_elim (tables ds) live2 c1) as [live1 c1'] eqn:?.
    inversion H.
    subst live' c'.
    clear H.
    eapply IHc1 in Heqo; [| eauto | eauto | eauto].
    destruct Heqo; intuition.
    eapply IHc2 in Heqp; [| eauto | eauto | eauto].
    destruct Heqp; intuition.
    simpl.
    exists x0.
    rewrite H3.
    eauto.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.


