(*

This file contains a formalization of
Dunfield's original system and a variant
with switch expression.

*)

Require Import Metalib.Metatheory.
Require Import LibTactics.

Require Import syntax.
Require Import typing.

(**********************************)
(*** Dunfield's Original System ***)
(**********************************)

(*

dexp consists of exressions as in Dunfield's
original system.

*)

Inductive dexp : Set :=  (*dunfield expression *)
 | de_var_b  : nat -> dexp
 | de_var_f  : var -> dexp
 | de_lit    : nat -> dexp
 | de_abs    : dexp -> dexp
 | de_app    : dexp -> dexp -> dexp
 | de_merg   : dexp -> dexp -> dexp
 | de_fix    : dexp -> dexp.


Fixpoint dopen_exp_wrt_exp_rec (k:nat) (e_5:dexp) (e__6:dexp) {struct e__6}: dexp :=
  match e__6 with
  | (de_var_b nat)  => if (k == nat) then e_5 else (de_var_b nat)
  | (de_var_f x)    => de_var_f x
  | (de_lit i5)     => de_lit i5
  | (de_abs e)      => de_abs (dopen_exp_wrt_exp_rec (S k) e_5 e)
  | (de_app e1 e2)  => de_app (dopen_exp_wrt_exp_rec k e_5 e1) (dopen_exp_wrt_exp_rec k e_5 e2)
  | (de_merg e1 e2) => de_merg (dopen_exp_wrt_exp_rec k e_5 e1) (dopen_exp_wrt_exp_rec k e_5 e2)
  | (de_fix e)      => de_fix (dopen_exp_wrt_exp_rec (S k) e_5 e)
end.

Definition dopen_exp_wrt_exp e_5 e__6 := dopen_exp_wrt_exp_rec 0 e__6 e_5.

(** Notation for opening up binders with type or term variables *)

Notation "t 'dopen_ee_var' x" := (dopen_exp_wrt_exp t (de_var_f x)) (at level 67).


(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive dlc_exp : dexp -> Prop :=    (* defn lc_exp *)
 | dlc_e_var_f : forall (x:var),
     (dlc_exp (de_var_f x))
 | dlc_e_lit : forall i5,
     (dlc_exp (de_lit i5))
 | dlc_e_abs : forall (L:vars) (e:dexp),
      ( forall x , x \notin  L  -> dlc_exp  (dopen_exp_wrt_exp e (de_var_f x)))  ->
     (dlc_exp (de_abs e))
 | dlc_e_app : forall (e1 e2:dexp),
     (dlc_exp e1) ->
     (dlc_exp e2) ->
     (dlc_exp (de_app e1 e2))
 | dlc_e_merg : forall (e1:dexp) (e2:dexp),
     (dlc_exp e1) ->
     (dlc_exp e2) ->
     (dlc_exp (de_merg e1 e2))
 (* | dlc_e_top :
      dlc_exp de_top *)
 | dlc_fix : forall (L:vars) (e:dexp),
      (forall x , x \notin L -> dlc_exp (dopen_exp_wrt_exp e (de_var_f x)) )  ->
      dlc_exp (de_fix e).

#[export]
Hint Constructors dlc_exp : core.

(** free variables *)
Fixpoint dfv_exp (e_5:dexp) : vars :=
  match e_5 with
  | (de_var_b nat) => {}
  | (de_var_f x) => {{x}}
  | (de_lit i5) => {}
  | (de_abs e) => (dfv_exp e)
  | (de_app e1 e2) => (dfv_exp e1) \u (dfv_exp e2)
  | (de_merg e1 e2) => (dfv_exp e1) \u (dfv_exp e2)
  (* | (de_top)       => {} *)
  | (de_fix e) => dfv_exp e
end.

(** substitutions *)
Fixpoint dsubst_exp (e_5:dexp) (x5:var) (e__6:dexp) {struct e__6} : dexp :=
  match e__6 with
  | (de_var_b nat) => de_var_b nat
  | (de_var_f x) => (if x == x5 then e_5 else (de_var_f x))
  | (de_lit i5) => de_lit i5
  | (de_abs e) => de_abs (dsubst_exp e_5 x5 e)
  | (de_app e1 e2) => de_app (dsubst_exp e_5 x5 e1) (dsubst_exp e_5 x5 e2)
  | (de_merg e1 e2) => de_merg (dsubst_exp e_5 x5 e1) (dsubst_exp e_5 x5 e2)
  (* | (de_top)    => de_top *)
  | (de_fix e) => de_fix (dsubst_exp e_5 x5 e)
end.

(*

Values as in original Dunfield's system

*)

Inductive dvalue : dexp -> Prop :=    (* defn value *)
 | dval_var : forall x,
     dvalue (de_var_f x)
 | dval_int : forall i5,
     dvalue (de_lit i5)
 | dval_abs : forall (e:dexp),
     dlc_exp (de_abs e) ->
     dvalue (de_abs e)
 | dval_merg : forall v1 v2,
    dvalue v1 ->
    dvalue v2 ->
    dvalue (de_merg v1 v2).

#[export]
Hint Constructors dvalue : core.

(* Dunfield's semantics *)

(* defns Reduction *)


(*

dstep corresponds to Dunfield's original semantics.

*)

Inductive dstep : dexp -> dexp -> Prop :=    (* defn step *)
 | dstep_appl : forall (e1 e2 e1':dexp),
     dlc_exp e2 ->
     dstep e1 e1' ->
     dstep (de_app e1 e2) (de_app e1' e2)
 | dstep_appr : forall (v e e':dexp),
     dvalue v ->
     dstep e e' ->
     dstep (de_app v e) (de_app v e')
 | dstep_beta : forall (e:dexp) v,
     dlc_exp (de_abs e) ->
     dvalue v ->
     dstep (de_app (de_abs e) v) (dopen_exp_wrt_exp e v)
 | dstep_mergl : forall (e1 e2 e1':dexp),
     dlc_exp e2 ->
     dstep e1 e1' ->
     dstep (de_merg e1 e2) (de_merg e1' e2)
 | dstep_mergr : forall (v e e':dexp),
     (* dvalue v -> *)
     dlc_exp v ->
     dstep e e' ->
     dstep (de_merg v e)  (de_merg v e')
 | dstep_unmergl : forall (e1 e2:dexp),
     dlc_exp e1 ->
     dlc_exp e2 ->
     dstep (de_merg e1 e2)  e1
 | dstep_unmergr : forall (e1 e2:dexp),
     dlc_exp e1 ->
     dlc_exp e2 ->
     dstep (de_merg e1 e2)  e2
 | dstep_split : forall (e:dexp),
     dlc_exp e ->
     dstep e (de_merg e e)
 | dstep_fix : forall e,
     dlc_exp (de_fix e) ->
     dstep (de_fix e) (dopen_exp_wrt_exp e (de_fix e)).

#[export]
Hint Constructors dstep : core.



(*******************************************************)
(****** Dunfield's system with switch expression *******)
(*******************************************************)

(*

dexp2 corresponds to expressions in Figure 1 in paper.

*)

Inductive dexp2 : Set :=  (*dunfield expression with switch *)
 | de_var_b2  : nat -> dexp2
 | de_var_f2  : var -> dexp2
 | de_lit2    : nat -> dexp2
 | de_abs2    : dexp2 -> dexp2
 | de_app2    : dexp2 -> dexp2 -> dexp2
 | de_merg2   : dexp2 -> dexp2 -> dexp2
 | de_fix2    : dexp2 -> dexp2
 | de_typeof2 : dexp2 -> dexp2 -> dexp2 -> dexp2.

 
Fixpoint dopen_exp_wrt_exp_rec2 (k:nat) (e_5:dexp2) (e__6:dexp2) {struct e__6}: dexp2 :=
  match e__6 with
  | (de_var_b2 nat)  => if (k == nat) then e_5 else (de_var_b2 nat)
  | (de_var_f2 x)    => de_var_f2 x
  | (de_lit2 i5)     => de_lit2 i5
  | (de_abs2 e)      => de_abs2 (dopen_exp_wrt_exp_rec2 (S k) e_5 e)
  | (de_app2 e1 e2)  => de_app2 (dopen_exp_wrt_exp_rec2 k e_5 e1) (dopen_exp_wrt_exp_rec2 k e_5 e2)
  | (de_merg2 e1 e2) => de_merg2 (dopen_exp_wrt_exp_rec2 k e_5 e1) (dopen_exp_wrt_exp_rec2 k e_5 e2)
  (* | (de_top)          => de_top *)
  | (de_fix2 e)      => de_fix2 (dopen_exp_wrt_exp_rec2 (S k) e_5 e)
  | (de_typeof2 e e1 e2) => de_typeof2 (dopen_exp_wrt_exp_rec2 k e_5 e) (dopen_exp_wrt_exp_rec2 (S k) e_5 e1) (dopen_exp_wrt_exp_rec2 (S k) e_5 e2)
end.

Definition dopen_exp_wrt_exp2 e_5 e__6 := dopen_exp_wrt_exp_rec2 0 e__6 e_5.

(** Notation for opening up binders with type or term variables *)

Notation "t 'dopen_ee_var2' x" := (dopen_exp_wrt_exp2 t (de_var_f2 x)) (at level 67).


(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive dlc_exp2 : dexp2 -> Prop :=    (* defn lc_exp *)
 | dlc_e_var_f2 : forall (x:var),
     (dlc_exp2 (de_var_f2 x))
 | dlc_e_lit2 : forall i5,
     (dlc_exp2 (de_lit2 i5))
 | dlc_e_abs2 : forall (L:vars) (e:dexp2),
      ( forall x , x \notin  L  -> dlc_exp2  (dopen_exp_wrt_exp2 e (de_var_f2 x)))  ->
     (dlc_exp2 (de_abs2 e))
 | dlc_e_app2 : forall (e1 e2:dexp2),
     (dlc_exp2 e1) ->
     (dlc_exp2 e2) ->
     (dlc_exp2 (de_app2 e1 e2))
 | dlc_e_merg2 : forall (e1:dexp2) (e2:dexp2),
     (dlc_exp2 e1) ->
     (dlc_exp2 e2) ->
     (dlc_exp2 (de_merg2 e1 e2))
 (* | dlc_e_top :
      dlc_exp de_top *)
 | dlc_fix2 : forall (L:vars) (e:dexp2),
      (forall x , x \notin L -> dlc_exp2 (dopen_exp_wrt_exp2 e (de_var_f2 x)) )  ->
      dlc_exp2 (de_fix2 e)
 | dlc_e_typeof2 : forall (L:vars) (e:dexp2) (e1:dexp2) (e2:dexp2),
     (dlc_exp2 e) ->
     ( forall x , x \notin  L  -> dlc_exp2  (dopen_exp_wrt_exp2 e1 (de_var_f2 x) )  ) ->
     ( forall x , x \notin  L  -> dlc_exp2  (dopen_exp_wrt_exp2 e2 (de_var_f2 x) )  ) ->
     (dlc_exp2 (de_typeof2 e e1 e2)).

#[export]
Hint Constructors dlc_exp2 : core.

(** free variables *)
Fixpoint dfv_exp2 (e_5:dexp2) : vars :=
  match e_5 with
  | (de_var_b2 nat) => {}
  | (de_var_f2 x) => {{x}}
  | (de_lit2 i5) => {}
  | (de_abs2 e) => (dfv_exp2 e)
  | (de_app2 e1 e2) => (dfv_exp2 e1) \u (dfv_exp2 e2)
  | (de_merg2 e1 e2) => (dfv_exp2 e1) \u (dfv_exp2 e2)
  | (de_fix2 e) => dfv_exp2 e
  | (de_typeof2 e e1 e2) => (dfv_exp2 e) \u (dfv_exp2 e1) \u (dfv_exp2 e2)
end.

(** substitutions *)
Fixpoint dsubst_exp2 (e_5:dexp2) (x5:var) (e__6:dexp2) {struct e__6} : dexp2 :=
  match e__6 with
  | (de_var_b2 nat) => de_var_b2 nat
  | (de_var_f2 x) => (if x == x5 then e_5 else (de_var_f2 x))
  | (de_lit2 i5) => de_lit2 i5
  | (de_abs2 e) => de_abs2 (dsubst_exp2 e_5 x5 e)
  | (de_app2 e1 e2) => de_app2 (dsubst_exp2 e_5 x5 e1) (dsubst_exp2 e_5 x5 e2)
  | (de_merg2 e1 e2) => de_merg2 (dsubst_exp2 e_5 x5 e1) (dsubst_exp2 e_5 x5 e2)
  | (de_fix2 e) => de_fix2 (dsubst_exp2 e_5 x5 e)
  | (de_typeof2 e e1 e2) => de_typeof2 (dsubst_exp2 e_5 x5 e) (dsubst_exp2 e_5 x5 e1) (dsubst_exp2 e_5 x5 e2)
end.

(*

dvalue2 corresponds to values shown in Figure 1 in paper

*)

Inductive dvalue2 : dexp2 -> Prop :=    (* defn value *)
 | dval_var2 : forall x,
     dvalue2 (de_var_f2 x)
 | dval_int2 : forall i5,
     dvalue2 (de_lit2 i5)
 | dval_abs2 : forall (e:dexp2),
     dlc_exp2 (de_abs2 e) ->
     dvalue2 (de_abs2 e)
 | dval_merg2 : forall v1 v2,
    dvalue2 v1 ->
    dvalue2 v2 ->
    dvalue2 (de_merg2 v1 v2).

#[export]
Hint Constructors dvalue2 : core.


(* Dunfield's semantics with switch expression *)

(*

dstep2 corresponds to semantics shown in Figure 3 in paper.

*)

Inductive dstep2 : dexp2 -> dexp2 -> Prop :=
 | dstep_appl2 : forall (e1 e2 e1':dexp2),
     dlc_exp2 e2 ->
     dstep2 e1 e1' ->
     dstep2 (de_app2 e1 e2) (de_app2 e1' e2)
 | dstep_appr2 : forall (v e e':dexp2),
     dvalue2 v ->
     dstep2 e e' ->
     dstep2 (de_app2 v e) (de_app2 v e')
 | dstep_beta2 : forall (e:dexp2) v,
     dlc_exp2 (de_abs2 e) ->
     dvalue2 v ->
     dstep2 (de_app2 (de_abs2 e) v) (dopen_exp_wrt_exp2 e v)
 | dstep_mergl2 : forall (e1 e2 e1':dexp2),
     dlc_exp2 e2 ->
     dstep2 e1 e1' ->
     dstep2 (de_merg2 e1 e2) (de_merg2 e1' e2)
 | dstep_mergr2 : forall (v e e':dexp2),
     (* dvalue v -> *)
     dlc_exp2 v ->
     dstep2 e e' ->
     dstep2 (de_merg2 v e)  (de_merg2 v e')
 | dstep_unmergl2 : forall (e1 e2:dexp2),
     dlc_exp2 e1 ->
     dlc_exp2 e2 ->
     dstep2 (de_merg2 e1 e2)  e1
 | dstep_unmergr2 : forall (e1 e2:dexp2),
     dlc_exp2 e1 ->
     dlc_exp2 e2 ->
     dstep2 (de_merg2 e1 e2)  e2
 | dstep_split2 : forall (e:dexp2),
     dlc_exp2 e ->
     dstep2 e (de_merg2 e e)
 | dstep_fix2 : forall e,
     dlc_exp2 (de_fix2 e) ->
     dstep2 (de_fix2 e) (dopen_exp_wrt_exp2 e (de_fix2 e))
 | dstep_typeof2 : forall (e:dexp2) (e1:dexp2) (e2 e':dexp2),
     dstep2 e e' ->
     dstep2 (de_typeof2 e e1 e2) (de_typeof2 e' e1 e2)
 | dstep_typeofl2 : forall (p :dexp2) (e1 e2:dexp2),
     dvalue2 p ->
     dstep2 (de_typeof2 p e1 e2)  (dopen_exp_wrt_exp2 e1 p)
 | dstep_typeofr2 : forall (p:dexp2) (e1 e2:dexp2),
     dvalue2 p ->
     dstep2 (de_typeof2 p e1 e2)  (dopen_exp_wrt_exp2 e2 p).

#[export]
Hint Constructors dstep2 : core.


(*

dtyping2 is the Dunfield's type system with
switch expression (without elaboration).

*)

Inductive dtyping2 : ctx -> dexp2 -> typ -> Prop :=
 | dtyp_lit2 : forall (G:ctx) i5,
      uniq G ->
      dtyping2 G (de_lit2 i5) t_int
 | dtyp_var2 : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
      dtyping2 G (de_var_f2 x) A
 | dtyp_merg12 : forall (G:ctx) (e1 e2:dexp2) (A:typ),
     dtyping2 G e1 A ->
     dtyping2 G (de_merg2 e1 e2) A
 | dtyp_merg22 : forall (G:ctx) (e1 e2:dexp2) (A:typ),
     dtyping2 G e2 A ->
     dtyping2 G (de_merg2 e1 e2) A
 | dtyp_abs2 : forall (L:vars) (G:ctx) (e:dexp2) A B,
     (forall x , x \notin L -> dtyping2 ([(x, A)] ++ G) (dopen_exp_wrt_exp2 e (de_var_f2 x)) B )  ->
     dtyping2 G (de_abs2 e) (t_arrow A B)
 | dtyp_app2 : forall (G:ctx) (e1 e2:dexp2) (B A:typ),
     dtyping2 G e1 (t_arrow A B) ->
     dtyping2 G e2 A ->
     dtyping2 G (de_app2 e1 e2) B
 | dtyp_and2: forall G e A B,
     dtyping2 G e A ->
     dtyping2 G e B ->
     dtyping2 G e (t_and A B)
 | dtyp_andl2: forall G e A B,
     dtyping2 G e (t_and A B) ->
     dtyping2 G e A
 | dtyp_andr2: forall G e A B,
     dtyping2 G e (t_and A B) ->
     dtyping2 G e B
 | dtyp_orl2 : forall G e A B,
     dtyping2 G e A ->
     dtyping2 G e (t_union A B)
 | dtyp_orr2 : forall G e A B,
     dtyping2 G e B ->
     dtyping2 G e (t_union A B)
 | dtyp_sub2 : forall (G:ctx) (e:dexp2) (A B:typ),
     dtyping2 G e B ->
     B <: A ->
     dtyping2 G e A
 | dtyp_fix2 : forall L e G A,
     (forall x, x \notin L -> dtyping2 ([(x, A)] ++ G) (dopen_exp_wrt_exp2 e (de_var_f2 x)) A) ->
     dtyping2 G (de_fix2 e) A
 | (*encoding switch expression in Dunfield's system*)
   dtyp_typeof2 : forall (L:vars) (G:ctx) (e:dexp2) (A:typ) (e1:dexp2) (B:typ) (e2:dexp2) (C:typ),
     dtyping2 G e (t_union A B) ->
     (forall x , x \notin  L  -> dtyping2 ([(x, A)] ++ G) (dopen_exp_wrt_exp2 e1 (de_var_f2 x)) C ) ->
     (forall x , x \notin  L  -> dtyping2 ([(x, B)] ++ G) (dopen_exp_wrt_exp2 e2 (de_var_f2 x)) C ) ->
     dtyping2 G  (de_typeof2 e e1 e2) C.

#[export]
Hint Constructors dtyping2 : core.


(***************************************************
Dunfield's original type system and
   elaboration to a variant with switch expression.
****************************************************)

(**********************************************)
(*** Evaluation context for Dunfield system ***)
(**********************************************)

Inductive dcvalctx :=
    | dctx_hole : dcvalctx
    | dctx_appl (E:dcvalctx) (e:dexp)
    | dctx_appr (v:dexp) (E:dcvalctx)
    | dctx_mergl (E:dcvalctx) (e:dexp)
    | dctx_mergr (e:dexp) (E:dcvalctx).

Fixpoint dfill E (x:dexp) :=
    match E with
    | dctx_hole => x
    | dctx_appl E' e  => de_app (dfill E' x) e
    | dctx_appr v E'  => de_app v (dfill E' x)
    | dctx_mergl E' e => de_merg (dfill E' x) e
    | dctx_mergr v E' => de_merg v (dfill E' x)
    end.

Inductive dwefctx : dcvalctx -> Prop :=
  | dctxhole : dwefctx dctx_hole
  | dctxappl : forall e E,
      dlc_exp e ->
      dwefctx E ->
      dwefctx (dctx_appl E e)
  | dctxappr : forall v E,
      dvalue v ->
      dwefctx E ->
      dwefctx (dctx_appr v E)
  | dctxmergl : forall e E,
      dlc_exp e ->
      dwefctx E ->
      dwefctx (dctx_mergl E e)
  | dctxmergrl : forall v E,
      dlc_exp v ->
      dwefctx E ->
      dwefctx (dctx_mergr v E).

(*
dtyping is Dunfield's original type system with
elaboration to a variant with switch expression.
*)

Inductive dtyping : ctx -> dexp -> typ -> dexp2 -> Prop :=
 | dtyp_lit : forall (G:ctx) i5,
      uniq G ->
      dtyping G (de_lit i5) t_int (de_lit2 i5)
 | dtyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
      dtyping G (de_var_f x) A (de_var_f2 x)
 | dtyp_merg1 : forall (G:ctx) (e1 e2:dexp) e3 (A:typ),
     dtyping G e1 A e3 ->
     dtyping G (de_merg e1 e2) A e3
 | dtyp_merg2 : forall (G:ctx) (e1 e2:dexp) e4 (A:typ),
     dtyping G e2 A e4 ->
     dtyping G (de_merg e1 e2) A e4
 | dtyp_abs : forall (L:vars) (G:ctx) (e:dexp) e' A B,
     (forall x , x \notin L -> dtyping ([(x, A)] ++ G) (dopen_exp_wrt_exp e (de_var_f x)) B (dopen_exp_wrt_exp2 e' (de_var_f2 x)))  ->
     dtyping G (de_abs e) (t_arrow A B) (de_abs2 e')
 | dtyp_app : forall (G:ctx) (e1 e2:dexp) e3 e4 (B A:typ),
     dtyping G e1 (t_arrow A B) e3 ->
     dtyping G e2 A e4 ->
     dtyping G (de_app e1 e2) B (de_app2 e3 e4)
 | dtyp_and: forall G e A B e1 e2,
     dtyping G e A e1 ->
     dtyping G e B e2 ->
     dtyping G e (t_and A B) (de_merg2 e1 e2)
 | dtyp_andl: forall G e A B e',
     dtyping G e (t_and A B) e' ->
     dtyping G e A e'
 | dtyp_andr: forall G e A B e',
     dtyping G e (t_and A B) e' ->
     dtyping G e B e'
 | dtyp_orl : forall G e A B e',
     dtyping G e A e' ->
     dtyping G e (t_union A B) e'
 | dtyp_orr : forall G e A B e',
     dtyping G e B e' ->
     dtyping G e (t_union A B) e'
 | dtyp_sub : forall (G:ctx) (e:dexp) (A B:typ) e',
     dtyping G e B e' ->
     B <: A ->
     dtyping G e A e'
 | dtyp_fix : forall L e G A e',
     (forall x, x \notin L -> dtyping ([(x, A)] ++ G) (dopen_exp_wrt_exp e (de_var_f x)) A (dopen_exp_wrt_exp2 e' (de_var_f2 x))) ->
     dtyping G (de_fix e) A (de_fix2 e')
 | (*encoding switch expression in Dunfield's system*)
   dtyp_typeof : forall (L:vars) (G:ctx) (e:dexp) (A:typ) e1 (B:typ) e2 (C:typ) e' E,
     dtyping G e (t_union A B) e' ->
     (forall x , x \notin  L  -> dtyping ([(x, A)] ++ G) (dfill E (de_var_f x)) C (dopen_exp_wrt_exp2 e1 (de_var_f2 x))) ->
     (forall x , x \notin  L  -> dtyping ([(x, B)] ++ G) (dfill E (de_var_f x)) C (dopen_exp_wrt_exp2 e2 (de_var_f2 x))) ->
     dtyping G (dfill E e) C (de_typeof2 e' e1 e2).

#[export]
Hint Constructors dtyping : core.

(*

dtyping3 corresponds to type system shown in Figure 2
in paper.

A variant of Dunfield's type system (with switch expression)
with elaboration to \m.

*)


Inductive dtyping3 : ctx -> dexp2 -> typ -> exp -> Prop :=
 | dtyp_lit3 : forall (G:ctx) i5,
      uniq G ->
      dtyping3 G (de_lit2 i5) t_int (e_lit i5)
 | dtyp_var3 : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
      dtyping3 G (de_var_f2 x) A (e_var_f x)
 | dtyp_merg13 : forall (G:ctx) (e1 e2:dexp2) e3 (A:typ),
     dtyping3 G e1 A e3 ->
     dtyping3 G (de_merg2 e1 e2) A e3
 | dtyp_merg23 : forall (G:ctx) (e1 e2:dexp2) e3 (A:typ),
     dtyping3 G e2 A e3 ->
     dtyping3 G (de_merg2 e1 e2) A e3
 | dtyp_abs3 : forall (L:vars) (G:ctx) (e:dexp2) e' A B,
     (forall x , x \notin L -> dtyping3 ([(x, A)] ++ G) (dopen_exp_wrt_exp2 e (de_var_f2 x)) B (open_exp_wrt_exp e' (e_var_f x)))  ->
     dtyping3 G (de_abs2 e) (t_arrow A B) (e_abs e' A B)
 | dtyp_app3 : forall (G:ctx) (e1 e2:dexp2) (B A:typ) e3 e4,
     dtyping3 G e1 (t_arrow A B) e3 ->
     dtyping3 G e2 A e4 ->
     dtyping3 G (de_app2 e1 e2) B (e_app e3 e4)
 | dtyp_and3: forall G e A B e1 e2,
     dtyping3 G e A e1 ->
     dtyping3 G e B e2 ->
     dtyping3 G e (t_and A B) (e_merg e1 e2)
 | dtyp_andl3: forall G e A B e',
     dtyping3 G e (t_and A B) e' ->
     dtyping3 G e A e'
 | dtyp_andr3: forall G e A B e',
     dtyping3 G e (t_and A B) e' ->
     dtyping3 G e B e'
 | dtyp_orl3 : forall G e A B e',
     dtyping3 G e A e' ->
     dtyping3 G e (t_union A B) e'
 | dtyp_orr3 : forall G e A B e',
     dtyping3 G e B e' ->
     dtyping3 G e (t_union A B) e'
 | dtyp_sub3 : forall (G:ctx) (e:dexp2) (A B:typ) e',
     dtyping3 G e B e'->
     B <: A ->
     dtyping3 G e A e'
 | dtyp_fix3 : forall L e G A e',
     (forall x, x \notin L -> dtyping3 ([(x, A)] ++ G) (dopen_exp_wrt_exp2 e (de_var_f2 x)) A (open_exp_wrt_exp e' (e_var_f x))) ->
     dtyping3 G (de_fix2 e) A (e_fix e'  A)
 | (*encoding switch expression in Dunfield's system*)
   dtyp_typeof3 : forall (L:vars) (G:ctx) (e:dexp2) (A:typ) (e1:dexp2) (B:typ) (e2:dexp2) (C:typ) e' e1' e2',
     dtyping3 G e (t_union A B) e' ->
     (forall x , x \notin  L  -> dtyping3 ([(x, A)] ++ G) (dopen_exp_wrt_exp2 e1 (de_var_f2 x)) C (open_exp_wrt_exp e1' (e_var_f x))) ->
     (forall x , x \notin  L  -> dtyping3 ([(x, B)] ++ G) (dopen_exp_wrt_exp2 e2 (de_var_f2 x)) C (open_exp_wrt_exp e2' (e_var_f x))) ->
     dtyping3 G  (de_typeof2 e e1 e2) C (e_typeof e' A e1' B e2').

#[export]
Hint Constructors dtyping3 : core.

(**************************************************************)
(** Dunfield's type system with switch (without elaboration) **)
(**************************************************************)

Inductive dtyping4 : ctx -> dexp2 -> typ -> Prop :=
 | dtyp_lit4 : forall (G:ctx) i5,
      uniq G ->
      dtyping4 G (de_lit2 i5) t_int
 | dtyp_var4 : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
      dtyping4 G (de_var_f2 x) A
 | dtyp_merg14 : forall (G:ctx) (e1 e2:dexp2) (A:typ),
     dtyping4 G e1 A ->
     dtyping4 G (de_merg2 e1 e2) A
 | dtyp_merg24 : forall (G:ctx) (e1 e2:dexp2) (A:typ),
     dtyping4 G e2 A ->
     dtyping4 G (de_merg2 e1 e2) A
 | dtyp_abs4 : forall (L:vars) (G:ctx) (e:dexp2) A B,
     (forall x , x \notin L -> dtyping4 ([(x, A)] ++ G) (dopen_exp_wrt_exp2 e (de_var_f2 x)) B )  ->
     dtyping4 G (de_abs2 e) (t_arrow A B)
 | dtyp_app4 : forall (G:ctx) (e1 e2:dexp2) (B A:typ),
     dtyping4 G e1 (t_arrow A B) ->
     dtyping4 G e2 A ->
     dtyping4 G (de_app2 e1 e2) B
 | dtyp_and4: forall G e A B,
     dtyping4 G e A ->
     dtyping4 G e B ->
     dtyping4 G e (t_and A B)
 | dtyp_andl4: forall G e A B,
     dtyping4 G e (t_and A B) ->
     dtyping4 G e A
 | dtyp_andr4: forall G e A B,
     dtyping4 G e (t_and A B) ->
     dtyping4 G e B
 | dtyp_orl4 : forall G e A B,
     dtyping4 G e A ->
     dtyping4 G e (t_union A B)
 | dtyp_orr4 : forall G e A B,
     dtyping4 G e B ->
     dtyping4 G e (t_union A B)
 | dtyp_sub4 : forall (G:ctx) (e:dexp2) (A B:typ),
     dtyping4 G e B ->
     B <: A ->
     dtyping4 G e A
 | dtyp_fix4 : forall L e G A,
     (forall x, x \notin L -> dtyping4 ([(x, A)] ++ G) (dopen_exp_wrt_exp2 e (de_var_f2 x)) A) ->
     dtyping4 G (de_fix2 e) A
 | (*encoding switch expression in Dunfield's system*)
   dtyp_typeof4 : forall (L:vars) (G:ctx) (e:dexp2) (A:typ) (e1:dexp2) (B:typ) (e2:dexp2) (C:typ),
     dtyping4 G e (t_union A B) ->
     (forall x , x \notin  L  -> dtyping4 ([(x, A)] ++ G) (dopen_exp_wrt_exp2 e1 (de_var_f2 x)) C) ->
     (forall x , x \notin  L  -> dtyping4 ([(x, B)] ++ G) (dopen_exp_wrt_exp2 e2 (de_var_f2 x)) C) ->
     dtyping4 G  (de_typeof2 e e1 e2) C.

#[export]
Hint Constructors dtyping4 : core.