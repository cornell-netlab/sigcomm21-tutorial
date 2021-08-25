Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List.
Import List.ListNotations.

Set Implicit Arguments.
Section Env.
  Variable (K V: Type).
  Context `{K_eq_dec: EquivDec.EqDec K eq}.
  Definition t := list (K * V).
  Definition emp: t := [].
  Definition diff_key (k: K) (b : K * V) :=
    if K_eq_dec k (fst b) then false else true.
  Definition bind (k: K) (v: V) (e: t) : t :=
    (k, v) :: filter (diff_key k) e.
  Fixpoint find (k: K) (e: t) : option V :=
    match e with
    | [] => None
    | (k', v) :: s =>
      if k == k'
      then Some v
      else find k s
    end.

  Lemma diff_key_eq:
    forall k v,
      diff_key k (k, v) = false.
  Proof.
    intros.
    cbv.
    destruct (K_eq_dec k k); congruence.
  Qed.

  Lemma filter_idem:
    forall A (f: A -> bool) l,
      filter f (filter f l) = filter f l.
  Proof.
    induction l.
    - reflexivity.
    - simpl.
      destruct (f a) eqn:?.
      * simpl.
        rewrite Heqb.
        congruence.
      * congruence.
  Qed.

  Lemma bind_overwrite:
    forall e k v v',
      bind k v' (bind k v e) = bind k v' e.
  Proof.
    unfold bind.
    simpl.
    intros.
    rewrite diff_key_eq.
    rewrite filter_idem.
    reflexivity.
  Qed.

  Lemma find_filter_neq:
    forall x y s,
      x <> y ->
      find x (filter (diff_key y) s) = find x s.
  Proof.
    intros.
    induction s.
    - reflexivity.
    - simpl.
      destruct a.
      destruct (diff_key y (k, v)) eqn:?.
      + cbv in Heqb.
        simpl.
        rewrite IHs.
        reflexivity.
      + rewrite IHs.
        cbv in Heqb.
        destruct (K_eq_dec y k), (equiv_dec x k); congruence.
  Qed.

  Lemma find_bind_neq:
    forall x y v s,
      x <> y ->
      Env.find x (Env.bind y v s) = Env.find x s.
  Proof.
    intros.
    simpl.
    destruct (equiv_dec x y); try congruence.
    rewrite find_filter_neq; eauto.
  Qed.

End Env.
