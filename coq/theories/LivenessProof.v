Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import MiniP4.Syntax.
Require MiniP4.Env.
Require Import MiniP4.Liveness.
Require Import MiniP4.Interp.
Open Scope string_scope.
Open Scope list_scope.

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

Lemma agree_trans:
  forall live x y z,
    agree live x y ->
    agree live y z ->
    agree live x z.
Proof.
  unfold agree.
  intros live x y z.
  rewrite !Forall_forall.
  intros.
  erewrite H; eauto.
Qed.

Lemma agree_sym:
  forall live x y,
    agree live x y ->
    agree live y x.
Proof.
  unfold agree.
  intros live x y.
  rewrite !Forall_forall.
  firstorder.
Qed.

Lemma agree_assign_dead:
  forall live s1 s2 x v,
    check x live = false ->
    agree live (store s1) (store s2) ->
    agree live (store (assign s1 x v)) (store (assign s2 x v)).
Proof.
  simpl.
  intros.
  eapply agree_trans.
  apply agree_bind_neq; auto.
  apply agree_sym.
  eapply agree_trans.
  apply agree_bind_neq; auto.
  apply agree_sym.
  apply H0.
Qed.

Lemma check_in:
  forall x s,
    check x s = true <-> In x s.
Proof.
  unfold check.
  intros x s.
  destruct (in_dec _ x s); intuition.
Qed.

Lemma agree_find:
  forall x live s1 s2,
    check x live = true ->
    agree live s1 s2 ->
    Env.find x s1 = Env.find x s2.
Proof.
  unfold agree.
  intros.
  rewrite Forall_forall in H0.
  eapply H0.
  apply check_in.
  auto.
Qed.

Lemma agree_emp:
  forall s1 s2,
    agree emp s1 s2.
Proof.
  intros.
  apply Forall_nil.
Qed.

Lemma agree_cons:
  forall a s e1 e2,
    Env.find a e1 = Env.find a e2 ->
    agree s e1 e2 ->
    agree (a :: s) e1 e2.
Proof.
  intros.
  apply Forall_cons; eauto.
Qed.

Lemma agree_union:
  forall s2 s1 e1 e2,
    agree (union s1 s2) e1 e2 ->
    agree s1 e1 e2 /\ 
    agree s2 e1 e2.
Proof.
  induction s2; simpl; intros.
  - eauto using agree_emp.
  - unfold add in H.
    destruct (check a s1) eqn:?.
    + apply IHs2 in H.
      intuition.
      eapply agree_cons; eauto.
      eapply Forall_forall in H0; eauto.
      eapply check_in; eauto.
    + apply IHs2 in H.
      intuition.
      * eapply Forall_forall.
        intros.
        eapply Forall_forall in H0.
        eapply H0.
        eauto with datatypes.
      * eapply agree_cons; eauto.
        eapply Forall_forall in H0; eauto.
        simpl; tauto.
Qed.

Lemma agree_union_l:
  forall s1 s2 e1 e2,
    agree (union s1 s2) e1 e2 ->
    agree s1 e1 e2.
Proof.
  intros.
  apply agree_union in H.
  tauto.
Qed.

Lemma agree_union_r:
  forall s1 s2 e1 e2,
    agree (union s1 s2) e1 e2 ->
    agree s2 e1 e2.
Proof.
  intros.
  apply agree_union in H.
  tauto.
Qed.

Lemma in_add_old:
  forall a b x,
    In a b ->
    In a (add x b).
Proof.
  intros.
  unfold add.
  destruct (check x b); eauto with datatypes.
Qed.

Lemma in_add:
  forall a b,
    In a (add a b).
Proof.
  intros.
  unfold add.
  destruct (check a b) eqn:?.
  - apply check_in; auto.
  - eauto with datatypes.
Qed.

Lemma in_union:
  forall b x a,
    In x (union a b) <->
    In x a \/ In x b.
Proof.
  induction b; intros; simpl in *.
  - tauto.
  - split; intros.
    + eapply IHb in H.
      intuition.
      destruct (name_eq_dec x a); eauto.
      unfold add in *.
      destruct (check a a0) eqn:?; subst.
      * eauto using check_in.
      * destruct H0; eauto.
    + intuition.
      * apply IHb.
        eauto using in_add_old.
      * apply IHb.
        left.
        subst.
        eapply in_add.
      * apply IHb; tauto.
Qed.

Lemma fold_left_union_inv:
  forall sets init x,
    In x (fold_left union sets init) ->
    (exists s, In s sets /\ In x s) \/ In x init.
Proof.
  induction sets.
  - simpl.
    eauto.
  - intros.
    simpl in H.
    eapply IHsets in H.
    destruct H as [[? [? ?]] | ?].
    + left.
      exists x0.
      eauto with datatypes.
    + eapply in_union in H.
      intuition.
      left.
      exists a.
      eauto with datatypes.
Qed.

Lemma fold_left_union_in:
  forall sets init x,
    (exists s, In s sets /\ In x s) \/ In x init ->
    In x (fold_left union sets init).
Proof.
  induction sets.
  - intros.
    firstorder.
  - intros.
    simpl in *.
    destruct H.
    + destruct H.
      intuition.
      * subst x0.
        apply IHsets.
        right.
        apply in_union.
        tauto.
      * apply IHsets.
        eauto using in_union with datatypes.
    + apply IHsets.
      right.
      eapply in_union; eauto.
Qed.

Lemma agree_union_all:
  forall sets s e1 e2,
    agree (union_all sets) e1 e2 ->
    In s sets ->
    agree s e1 e2.
Proof.
  unfold union_all, agree.
  intros.
  rewrite !Forall_forall in *.
  intros.
  eapply H.
  eapply fold_left_union_in; eauto.
Qed.

Lemma dse_exp_corr:
  forall s s' e,
    agree (fv e) s.(store) s'.(store) ->
    interp_exp s e = interp_exp s' e.
Proof.
  induction e; simpl; intros.
  - eapply agree_find; eauto.
    apply check_cons_eq.
  - reflexivity.
  - reflexivity.
  - apply agree_union in H; destruct H.
    rewrite IHe1 by eauto.
    rewrite IHe2 by eauto.
    reflexivity.
  - reflexivity.
  - rewrite IHe by eauto.
    reflexivity.
  - rewrite IHe by eauto.
    reflexivity.
  - apply agree_union in H; destruct H.
    rewrite IHe1 by eauto.
    rewrite IHe2 by eauto.
    reflexivity.
  - rewrite IHe by eauto.
    reflexivity.
Qed.

Lemma pkt_assign:
  forall s x v,
    pkt (assign s x v) = pkt s.
Proof.
  reflexivity.
Qed.

Lemma in_drop_neq:
  forall x y s,
    x <> y ->
    In x s ->
    In x (drop y s).
Proof.
  intros.
  unfold drop.
  apply in_in_remove; eauto.
Qed.

Lemma agree_bind:
  forall x live v s1 s2,
    agree (drop x live) s1 s2 ->
    agree live (Env.bind x v s1) (Env.bind x v s2).
Proof.
  intros.
  apply Forall_forall; intros.
  destruct (name_eq_dec x x0).
  - cbv in e.
    subst x0.
    rewrite !Env.find_bind_eq.
    reflexivity.
  - rewrite !Env.find_bind_neq by auto.
    eapply Forall_forall in H; eauto.
    apply in_drop_neq; eauto.
Qed.

Lemma agree_assign:
  forall live s1 s2 x v,
    agree (drop x live) (store s1) (store s2) ->
    agree live (store (assign s1 x v)) (store (assign s2 x v)).
Proof.
  simpl.
  intros.
  apply agree_bind; auto.
Qed.

Lemma agree_add:
  forall x s e1 e2,
    agree (add x s) e1 e2 ->
    agree s e1 e2.
Proof.
  unfold add.
  intros.
  destruct (check x s); eauto.
  eapply Forall_forall.
  intros.
  eapply Forall_forall in H; eauto with datatypes.
Qed.

Lemma dse_act_corr:
  forall act live live',
    act_live live act = live' ->
    forall s1 s1',
      interp_act s1 act = Some s1' ->
      forall s2,
        agree live' s1.(store) s2.(store) ->
        s1.(pkt) = s2.(pkt) ->
        exists s2',
          interp_act s2 act = Some s2' /\
          agree live s1'.(store) s2'.(store) /\
          s1'.(pkt) = s2'.(pkt).
Proof.
  induction act; simpl; intros.
  - subst live'.
    pose proof (agree_union_r _ _ _ _ H1).
    eapply dse_exp_corr with (s:=s1) (s':=s2) in H.
    erewrite H in *.
    destruct (interp_exp s2 e) eqn:?; simpl in * |-; try congruence.
    simpl.
    inversion H0; subst.
    eexists.
    intuition eauto.
    eapply agree_assign.
    eapply agree_union_l; eauto.
  - destruct (interp_act s1 act1) eqn:H'; try congruence.
    remember (act_live live act2) as live2.
    pose proof (H'' := H').
    eapply IHact1 in H''; eauto.
    destruct H''.
    intuition.
    rewrite H4.
    symmetry in H.
    eapply IHact2 in H0; eauto.
    congruence.
  - exists s2.
    intuition congruence.
Qed.

Lemma dse_cmd_corr:
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
    destruct (interp_exp s1 e) eqn:?; simpl in * |-; try congruence.
    destruct (check x live) eqn:?; inversion H; clear H; subst.
    + simpl.
      inversion H0; subst.
      pose proof (agree_union_r _ _ _ _ H1).
      apply dse_exp_corr in H.
      rewrite Heqo in *.
      rewrite H in *.
      destruct (interp_exp s2 e) eqn:?; simpl in *; try congruence.
      exists (assign s2 x v).
      erewrite !pkt_assign in *; eauto.
      inversion H.
      intuition.
      apply agree_assign.
      eapply agree_union_l; eauto.
    + exists s2.
      inversion H0; subst.
      clear H0.
      simpl; intuition.
      * eapply agree_trans.
        apply agree_bind_neq; eauto.
        eauto.
  - inversion H; subst.
    exists s2.
    destruct n; simpl in *; try congruence.
    intuition congruence.
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
  - destruct (dead_store_elim _ _ c1) eqn:?.
    destruct (dead_store_elim _ _ c2) eqn:?.
    inversion H.
    subst; clear H.
    destruct n; simpl in *; try congruence.
    assert (agree (fv e) (store s1) (store s2))
      by (eapply agree_union_all; eauto with datatypes).
    erewrite dse_exp_corr in * by eauto.
    destruct (interp_exp s2 e); try congruence.
    destruct (val_eq_dec v1 (VBits [true])).
    + cbv in e0.
      subst v1.
      eapply IHc1 in H0; eauto.
      eapply agree_union_all; eauto with datatypes.
    + destruct v1 as [ [ | [ | ] [ | ] ]| | | ];
        simpl in *;
        solve [eapply IHc2 in H0; eauto;
               eapply agree_union_all; eauto with datatypes
              |congruence].
  - inversion H; subst.
    destruct n; simpl in *; try congruence.
    destruct (Env.find x (type_env ds)); try congruence.
    unfold interp_extr in *.
    rewrite <- H2 in *.
    destruct (extr (pkt s1) t); try congruence.
    destruct p.
    inversion H0; subst.
    eexists; intuition eauto.
    simpl.
    eauto using agree_bind.
  - inversion H; subst.
    destruct n; simpl in *; try congruence.
    assert (Env.find x (store s1) = Env.find x (store s2)).
    {
      eapply Forall_forall in H1; eauto.
      apply check_in.
      apply check_add_eq.
    }
    rewrite H3 in *.
    destruct (Env.find x (store s2)); try congruence.
    unfold interp_emit in *.
    inversion H0; subst.
    eexists; intuition eauto.
    simpl.
    eapply agree_add; eauto.
  - destruct n; simpl in * |-; try congruence.
    destruct (Env.find t ds.(tables)) eqn:?; try congruence.
    inversion H; subst.
    clear H.
    simpl.
    rewrite Heqo.
    apply agree_union in H1; intuition.
    destruct (Env.find t ds.(rules)); try congruence.
    unfold interp_table in *.
    erewrite dse_exp_corr by eauto using agree_sym.
    destruct (interp_exp _ _); try congruence.
    destruct (find_rule _ _); try congruence.
    destruct (nth_in_or_default (rule_action r) (table_acts t0) ActNop).
    + remember (nth (rule_action r) (table_acts t0) ActNop) as act.
      simpl in *.
      eapply dse_act_corr; eauto.
      eapply agree_union_all; eauto.
      eapply in_map_iff.
      eexists; intuition eauto with datatypes.
    + rewrite e in *.
      simpl in *.
      eexists; intuition eauto.
      * inversion H0; subst.
        unfold acts_live in *.
        simpl in *.
        eapply agree_union_all; eauto with datatypes.
      * congruence.
Qed.

Print Assumptions dse_cmd_corr.
