
(*

This file contains Coq formalization of the soundness/completeness
of Dunfield's system to our system.

It also contains formalization of the completeness of
Dunfield's system with switch expression to original
Dunfield's system.

*)


Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import Lia.


Require Import syntax.
Require Import typing.
Require Import dunfield.
Require Import multi_step.

(*

dt_complete_our_system corresponds to Lemma 7 (Completeness Lemma)
in paper.

*)

Lemma dt_complete_our_system : forall G e1 e2 A,
    dtyping3 G e1 A e2 -> 
    typing G e2 A.
Proof.
    induction 1; intros; eauto.
Qed.


(*

erase corresponds to erasure function shown in Figure 8
in paper.

*)

(** erase *)
Fixpoint erase (e:exp) : dexp2 :=
  match e with
  | (e_var_b i) => de_var_b2 i
  | (e_var_f x) => de_var_f2 x
  | (e_lit i5) => de_lit2 i5
  (* | (e_ann e A) => erase e *)
  | (e_abs e A B) => de_abs2 (erase e)
  | (e_app e1 e2) => de_app2 (erase e1) (erase e2)
  | (e_merg e1 e2) => de_merg2 (erase e1) (erase e2)
  | (e_fix e A) => de_fix2 (erase e)
  | (e_typeof e A e1 B e2) => (de_typeof2 (erase e) (erase e1) (erase e2))
end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | e_var_f x1 => 1
    | e_var_b n1 => 1
    | e_lit i1 => 1
    | e_abs e2 A1 B1 => 1 + (t_size A1) + (size_exp e2) + (t_size B1)
    | e_fix e2 A1 => 1 + (t_size A1) + (size_exp e2)
    | e_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | e_merg e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    (* | e_ann e2 A1 => 1 + (size_exp e2) + (t_size A1) *)
    | e_typeof e A e1 B e2 => 1 + (size_exp e) + (t_size A) + (size_exp e1) + (t_size B) + (size_exp e2)
  end.

Lemma erase_open_aux : forall i,
    forall e, (size_exp e <= i -> forall t n, erase (open_exp_wrt_exp_rec n t e) = dopen_exp_wrt_exp_rec2 n (erase t) (erase e)).
Proof.
  intros i.
    induction i; intros; simpl in *.
  - (*case i = 0*) 
    destruct e; simpl in *; try solve [lia].
  - (*case i = S n*)
    induction e; simpl in *; intros; eauto.
    + (*case var n*)
      destruct (n == n0); auto.
    (* + case anno
      forwards*: IHe. lia. *)
    + (*case abs*)
      forwards*: IHi e t (S n). lia.
      rewrite H0. auto.
    + (*case app*)
      forwards*: IHe1. lia.
      forwards*: IHe2. lia.
      rewrite H0. rewrite H1. auto.
    + (*case merg*)
      forwards*: IHe1. lia.
      forwards*: IHe2. lia.
      rewrite H0. rewrite H1. auto.
    + forwards*: IHe1. lia. 
      forwards*: IHi e2 t (S n). lia.
      forwards*: IHi e3 t (S n). lia.
      rewrite H0. rewrite H1.
      rewrite H2. auto.
    + (*case fix*)
      forwards*: IHi e t (S n). lia.
      rewrite H0. auto.
Qed.

Lemma erase_open : forall e1 e2,
  erase (open_exp_wrt_exp e1 e2) =
  (dopen_exp_wrt_exp2 (erase e1) (erase e2)).
Proof.
  intros e1 e2.
  pose proof (erase_open_aux (size_exp e1)).
  eauto.
Qed.

Lemma erase_open_var : forall e x,
  (erase (e open_ee_var x)) =
  (erase e dopen_ee_var2 x).
Proof.
  intros e x.
  pose proof (erase_open_aux (size_exp e)).
  forwards*: H e (e_var_f x).
Qed.

Lemma erase_lc : forall e,
  lc_exp e -> dlc_exp2 (erase e).
Proof.
  induction 1; try solve [simpl in *; eauto]; simpl in *.
 - eapply dlc_e_abs2 with (L:=L). intros; eauto.
   forwards*: H0 x.
   rewrite erase_open_var in H2; auto.
 - eapply dlc_e_typeof2 with (L:=L); intros; eauto.
   forwards* TEMP1: H1.
   rewrite erase_open_var in TEMP1; auto.
   forwards* TEMP1: H3.
   rewrite erase_open_var in TEMP1; auto.
 - eapply dlc_fix2 with (L:=L); intros.
   forwards*: H0 x.
   rewrite erase_open_var in H2; auto.
Qed.

Lemma erase_value : forall e,
  value e -> dvalue2 (erase e).
Proof.
  introv VAL.
  induction VAL; simpl in *; auto.
  apply erase_lc in H; eauto.
Qed.


(*

dt_sound_our_system corresponds to Lemma 8 (Soundness Lemma)
in paper.

*)

Lemma dt_sound_our_system : forall G e A,
  typing G e A -> dtyping4 G (erase e) A.
Proof.
  induction 1; intros; simpl in *; eauto.
  - pick fresh y and apply dtyp_abs4.
    specialize (H0 y).
    rewrite <- erase_open_var. eauto.
  - pick fresh y and apply dtyp_typeof4; auto.
    apply IHtyping.
    rewrite <- erase_open_var. eauto.
    rewrite <- erase_open_var. eauto.
  - pick fresh y and apply dtyp_fix4.
    rewrite <- erase_open_var. eauto.
Qed.


Lemma tred_sound : forall v A v',
  value v ->
  tred v A v' ->
  mdstep (erase v) (erase v').
Proof.
  introv VAL Red.
  lets Red': Red.
  induction Red; intros;
  simpl; eauto.
  (*case merg1*)
  inverts* VAL.
  forwards* RED1: IHRed.
  eapply mdstep_trans with (e2:=(erase p1)); auto.
  apply dstep_unmergl2.
  apply value_regular in H3.
  apply erase_lc in H3; auto.
  apply value_regular in H4.
  apply erase_lc in H4; auto.
  (*case merg2*)
  inverts* VAL.
  forwards* RED1: IHRed.
  eapply mdstep_trans with (e2:=(erase p2)); auto.
  apply dstep_unmergr2.
  apply value_regular in H3.
  apply erase_lc in H3; auto.
  apply value_regular in H4.
  apply erase_lc in H4; auto.
  (*case and*)
  lets LC: VAL.
  apply value_regular in LC.
  apply erase_lc in LC.
  forwards* VAL1: tred_value Red1.
  forwards* VAL2: tred_value Red2. 
  forwards* Red3: IHRed1.
  forwards* Red4: IHRed2.
  clear Red1 Red2 IHRed1 IHRed2.
  eapply md_trans with (e2:=de_merg2 (erase p) (erase p)).
  eapply md_one.
  eapply dstep_split2.
  auto.
  eapply md_trans.
  eapply mdstep_mergel.
  apply Red3.
  auto.
  apply mdstep_merger; auto.
  apply value_regular in VAL1.
  apply* erase_lc.
Qed.

Lemma dvalue_regular : forall v,
  dvalue2 v -> dlc_exp2 v.
Proof.
  induction 1; auto.
Qed.


(*

dstep_sound_our_system corresponds to Lemma 9
(Soundness of Semantics) in paper.

*)

Lemma dstep_sound_our_system : forall e,
    forall e', step e e' ->
    mdstep (erase e) (erase e').
Proof.
    induction 1; simpl in *; eauto.
  - (*case appl*)
    induction IHstep; auto.
    eapply mdstep_trans with (e2:=(de_app2 e3 (erase e2))); eauto.
    apply dstep_appl2; auto.
    apply* erase_lc.
  - (*case appr*)
    induction IHstep; auto.
    eapply mdstep_trans with (e2:=(de_app2 (erase v) e2)); eauto.
    apply dstep_appr2; auto.
    apply* erase_value.
    (*case beta*)
  - rewrite~ erase_open.
    forwards*: tred_sound H1.
    forwards* VAL: tred_value H1.
    assert (VAL1: value p'); auto.
    apply erase_value in VAL1.
    induction H2; auto.
    (*sub case 1*)
    eapply mdstep_trans with (e2:=(dopen_exp_wrt_exp2 (erase e) e0)); auto.
    apply dstep_beta2; auto.
    apply erase_lc in H; simpl in H; auto.
    (*sub case 2*)
    eapply mdstep_trans with (e2:=(de_app2 (de_abs2 (erase e)) e2)); auto.
    apply dstep_appr2; auto.
    apply dval_abs2; eauto.
    apply erase_lc in H; simpl in H; auto.
  - (*case dyn semantics*)
    inverts H1; simpl in *.
      + (*sub case*)
      eapply mdstep_trans with (e2:=(de_app2 (erase p1) (erase v))); eauto.
      apply dstep_appl2.
      apply value_regular in H; auto.
      apply* erase_lc.
      apply value_regular in H0.
      apply erase_lc in H0. simpl in H0.
      inverts H0.
      apply* dstep_unmergl2.
    + (*sub case*)
      eapply mdstep_trans with (e2:=(de_app2 (erase p2) (erase v))); eauto.
      apply dstep_appl2.
      apply value_regular in H; auto.
      apply* erase_lc.
      apply value_regular in H0.
      apply erase_lc in H0. simpl in H0.
      inverts H0.
      apply* dstep_unmergr2.
    + (*sub case*)
      lets VAL1: H.
      lets VAL2: H0.
      apply value_regular in H.
      apply value_regular in H0; auto.
      apply erase_lc in H.
      apply erase_lc in H0. simpl in *.
      eapply mdstep_trans with (e2:=de_merg2 (de_app2 (de_merg2 (erase p1) (erase p2)) (erase v)) (de_app2 (de_merg2 (erase p1) (erase p2)) (erase v))); eauto.
      eapply mdstep_trans with (e2:=de_merg2 (de_app2 (erase p1) (erase v)) (de_app2 (de_merg2 (erase p1) (erase p2)) (erase v))); eauto.
      apply* dstep_mergl2.
      apply* dstep_appl2.
      inverts H0. apply* dstep_unmergl2.
      eapply mdstep_trans with (e2:=de_merg2 (de_app2 (erase p1) (erase v)) (de_app2 (erase p2) (erase v))); eauto.
      inverts H0.
      apply* dstep_mergr2.
  (* - case annov
      forwards*: tred_sound H0. *)
  - (*case merge 1*)
    induction IHstep; auto.
    eapply mdstep_trans with (e2:=(de_merg2 e3 (erase e2))); eauto.
    apply dstep_mergl2; auto.
    apply* erase_lc.
  - (*case merge 1*)
    induction IHstep; auto.
    eapply mdstep_trans with (e2:=(de_merg2 (erase v) e2)); eauto.
    apply erase_value in H.
    apply dvalue_regular in H. eauto.
  - (*case switch*)
    induction IHstep; auto.
    eapply mdstep_trans with (e2:=de_typeof2 e3 (erase e1) (erase e2)); auto.
  - rewrite~ erase_open.
    forwards*: tred_sound H1.
    forwards* VAL: tred_value H1.
    assert (VAL1: value p'); auto.
    apply erase_value in VAL1.
    induction H2; auto.
    (*sub case 1*)
    eapply mdstep_trans with (e2:=(dopen_exp_wrt_exp2 (erase e1) e)); auto.
    (*sub case 2*)
    eapply mdstep_trans with (e2:=de_typeof2 e3 (erase e1) (erase e2)); auto.
  - rewrite~ erase_open.
    forwards*: tred_sound H1.
    forwards* VAL: tred_value H1.
    assert (VAL1: value p'); auto.
    apply erase_value in VAL1.
    induction H2; auto.
    (*sub case 1*)
    eapply mdstep_trans with (e2:=(dopen_exp_wrt_exp2 (erase e2) e)); auto.
    (*sub case 2*)
    eapply mdstep_trans with (e2:=de_typeof2 e3 (erase e1) (erase e2)); auto.
  (*case fix*)
  - rewrite erase_open; simpl.
    eapply mdstep_trans; eauto.
    apply erase_lc in H; simpl in *; auto.
Qed.


(************************************************)
(* Completeness of Dunfield's original system to
a variant with switch expression ****************)
(************************************************)

(*

dt_dt2_complete shows that a variant of Dunfield's type
system with switch expression is complete to Dunfield's
original type system.

*)

Lemma dt_dt2_complete : forall G e1 e2 A,
    dtyping G e1 A e2 -> 
    dtyping2 G e2 A.
Proof.
    induction 1; intros; eauto.
Qed.

Lemma val_checks_top : forall G dv A e',
    dvalue dv ->
    dtyping G dv A e' ->
    dtyping G dv t_top e'.
Proof.
    induction 1; intros; eauto.
Qed.

Lemma val_checks_typ : forall G dv e',
    dtyping G dv t_top e' ->
    dtyping2 G e' t_top.
Proof.
    induction 1; intros; eauto.
Qed.

(* 

transform transforms Dunfield's original
expression to a variant with switch expression.

*)
Fixpoint transform (e:dexp) : dexp2 :=
  match e with
  | (de_var_b i) => de_var_b2 i
  | (de_var_f x) => de_var_f2 x
  | (de_lit i5) => de_lit2 i5
  | (de_abs e) => de_abs2 (transform e)
  | (de_app e1 e2) => de_app2 (transform e1) (transform e2)
  | (de_merg e1 e2) => de_merg2 (transform e1) (transform e2)
  | (de_fix e) => de_fix2 (transform e)
end.

Fixpoint size_exp2 (e1 : dexp) {struct e1} : nat :=
  match e1 with
    | de_var_f x1 => 1
    | de_var_b n1 => 1
    | de_lit i1 => 1
    | de_abs e2 => 1 + (size_exp2 e2)
    | de_fix e2 => 1 + (size_exp2 e2)
    | de_app e2 e3 => 1 + (size_exp2 e2) + (size_exp2 e3)
    | de_merg e2 e3 => 1 + (size_exp2 e2) + (size_exp2 e3)
  end.

Lemma transform_open_aux : forall i,
    forall e, (size_exp2 e <= i -> forall t n, transform (dopen_exp_wrt_exp_rec n t e) = dopen_exp_wrt_exp_rec2 n (transform t) (transform e)).
Proof.
  intros i.
    induction i; intros; simpl in *.
  - (*case i = 0*) 
    destruct e; simpl in *; try solve [lia].
  - (*case i = S n*)
    induction e; simpl in *; intros; eauto.
    + (*case var n*)
      destruct (n == n0); auto.
    + (*case abs*)
      forwards*: IHi e t (S n). lia.
      rewrite H0. auto.
    + (*case app*)
      forwards*: IHe1. lia.
      forwards*: IHe2. lia.
      rewrite H0. rewrite H1. auto.
    + (*case merg*)
      forwards*: IHe1. lia.
      forwards*: IHe2. lia.
      rewrite H0. rewrite H1. auto.
    + (*case fix*)
      forwards*: IHi e t (S n). lia.
      rewrite H0. auto.
Qed.

Lemma transform_open : forall e1 e2,
  transform (dopen_exp_wrt_exp e1 e2) =
  (dopen_exp_wrt_exp2 (transform e1) (transform e2)).
Proof.
  intros e1 e2.
  pose proof (transform_open_aux (size_exp2 e1)).
  eauto.
Qed.

Lemma transform_open_var : forall e x,
  (transform (e dopen_ee_var x)) =
  (transform e dopen_ee_var2 x).
Proof.
  intros e x.
  pose proof (transform_open_aux (size_exp2 e)).
  forwards*: H e (de_var_f x).
Qed.

Lemma transform_lc : forall e,
  dlc_exp e -> dlc_exp2 (transform e).
Proof.
  induction 1; try solve [simpl in *; eauto]; simpl in *.
 - eapply dlc_e_abs2 with (L:=L). intros; eauto.
   forwards*: H0 x.
   rewrite transform_open_var in H2; auto.
 - eapply dlc_fix2 with (L:=L); intros.
   forwards*: H0 x.
   rewrite transform_open_var in H2; auto.
Qed.

Lemma transform_value : forall e,
  dvalue e -> dvalue2 (transform e).
Proof.
  introv VAL.
  induction VAL; simpl in *; auto.
  apply transform_lc in H; eauto.
Qed.

(*
  step_dexp_dexp2_complete states the completeness of semantics
  of orginal Dunfield's system to a variant with switch
  expression
*)

Lemma dstep_dstep2_complete : forall e e',
  dstep e e' ->
  dstep2 (transform e) (transform e').
Proof.
  induction 1; simpl; eauto.
 - apply dstep_appl2; auto.
   apply* transform_lc.
 - apply dstep_appr2; auto.
   apply*  transform_value.
 - rewrite~ transform_open.
   apply dstep_beta2.
   apply transform_lc in H.
   simpl in H; auto.
   apply* transform_value.
 - apply dstep_mergl2; auto.
   apply* transform_lc.
 - apply dstep_mergr2; auto.
   apply* transform_lc.
 - apply dstep_unmergl2.
   apply* transform_lc.
   apply* transform_lc.
 - apply dstep_unmergr2.
   apply* transform_lc.
   apply* transform_lc.
 - apply dstep_split2.
   apply* transform_lc.
 - rewrite~ transform_open.
   apply dstep_fix2.
   apply transform_lc in H.
   simpl in H. auto.
Qed.