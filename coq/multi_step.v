
(*

This file contains the multi-step reduction relation
for Dunfield's system with switch expression.

*)

Require Import Metalib.Metatheory.
Require Import LibTactics.

Require Import dunfield.


(*
multi-step relation to show the soundness of semantics
*)

Reserved Notation "e ~~>*d e'" (at level 80).
Inductive mdstep : dexp2 -> dexp2 -> Prop :=
  | mdstep_refl : forall e,
      mdstep e e
  | mdstep_trans : forall e1 e2 e3,
      dstep2 e1 e2 ->
      mdstep e2 e3 ->
      mdstep e1 e3
where "e ~~>*d e'" := (mdstep e e') : env_scope.

#[export]
Hint Constructors mdstep : core.

Lemma md_trans : forall e1 e2,
    mdstep e1 e2 -> forall e3, mdstep e2 e3 ->
    mdstep e1 e3.
Proof.
  induction 1; intros; eauto.
Qed.

Lemma md_one : forall e1 e2,
  dstep2 e1 e2 ->
  mdstep e1 e2.
Proof.
  introv Red.
  eapply mdstep_trans with (e2:=e2); auto.
Qed.

Lemma mdstep_mergel : forall e1 e2 e1',
  mdstep e1 e1' -> dlc_exp2 e2 ->
  mdstep (de_merg2 e1 e2) (de_merg2 e1' e2).
Proof.
  induction 1; auto; intros.
  eapply md_trans.
  apply md_one.
  apply dstep_mergl2; auto.
  apply H. auto.
Qed.

Lemma mdstep_merger : forall e1 e2 e2',
  mdstep e2 e2' -> dlc_exp2 e1 ->
  mdstep (de_merg2 e1 e2) (de_merg2 e1 e2').
Proof.
  induction 1; auto; intros.
  eapply md_trans.
  apply md_one.
  apply dstep_mergr2; auto.
  apply H. auto.
Qed.