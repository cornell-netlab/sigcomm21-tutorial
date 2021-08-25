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
  
End Env.
