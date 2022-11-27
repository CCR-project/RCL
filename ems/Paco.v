Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From Ordinal Require Import Ordinal Arithmetic.
Require Import SimSTS.
From Paco Require Import pacotac_internal.

Set Implicit Arguments.
Set Primitive Projections.

(** ** Predicates of Arity 1
*)

Section Arg1_def.

Variable T0 : Type.
Variable gf : rel1 T0 -> rel1 T0.
Arguments gf : clear implicits.

Variant _paco (paco: rel1 T0 -> rel1 T0) ( r: rel1 T0) x0 : Prop :=
| paco_pfold pco
    (LE : pco <1= (paco r \1/ r))
    (SIM: gf pco x0)
.

CoInductive paco r x0 : Prop := paco_go { paco_observe: _paco paco r x0 }.

Definition upaco( r: rel1 T0) := paco r \1/ r.

End Arg1_def.

Arguments paco [ T0 ] gf r x0.
Arguments upaco [ T0 ] gf r x0.
#[export] Hint Unfold upaco : core.

(* Less than or equal - internal use only *)
Notation "p <_paco_1= q" :=
  (forall _paco_x0 (PR: p _paco_x0 : Prop), q _paco_x0 : Prop)
  (at level 50, no associativity).

(* coinduction automation - internal use only *)
Ltac paco_cofix_auto :=
  let CIH := fresh "CIH" in cofix CIH; repeat intro;
  match goal with [H: _ |- _] => apply paco_observe in H; destruct H as [] end; do 2 econstructor;
  try (match goal with [H: _|-_] => apply H end); intros;
  lazymatch goal with [PR: _ |- _] => match goal with [H: _ |- _] => apply H in PR end end;
  repeat match goal with [ H : _ \/ _ |- _] => destruct H end; first [eauto; fail|eauto 10].

Definition monotone T0 (gf: rel1 T0 -> rel1 T0) :=
  forall x0 r r' (IN: gf r x0) (LE: r <1= r'), gf r' x0.

Definition _monotone T0 (gf: rel1 T0 -> rel1 T0) :=
  forall r r'(LE: r <1= r'), gf r <1== gf r'.

Lemma monotone_eq T0 (gf: rel1 T0 -> rel1 T0) :
  monotone gf <-> _monotone gf.
Proof. unfold monotone, _monotone, le1. split; eauto. Qed.

Lemma paco_mon_gen T0 gf gf' r r' x
    (PR: @paco T0 gf r x)
    (LEgf: gf <2= gf')
    (LEr: r <1= r'):
  paco gf' r' x.
Proof.
  revert x PR. cofix CIH.
  intros. apply paco_observe in PR. destruct PR as [].
  do 2 econstructor.
  - intros. specialize (LE x0 PR). destruct LE.
    + left. apply CIH, H.
    + right. apply LEr, H.
  - apply LEgf, SIM.
Qed.

Section Arg1.

Variable T0 : Type.
Variable gf : rel1 T0 -> rel1 T0.
Arguments gf : clear implicits.

Theorem paco_acc: forall
  l r (OBG: forall rr (INC: r <1= rr) (CIH: l <1= rr), l <1= paco gf rr),
  l <1= paco gf r.
Proof.
  intros; assert (SIM: paco gf (r \1/ l) x0) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco_mon: monotone (paco gf).
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco_mult_strong: forall r,
  paco gf (upaco gf r) <1= paco gf r.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Corollary paco_mult: forall r,
  paco gf (paco gf r) <1= paco gf r.
Proof. intros; eapply paco_mult_strong, paco_mon; eauto. Qed.

Theorem paco_fold: forall r,
  gf (upaco gf r) <1= paco gf r.
Proof. intros; do 2 econstructor; [ |eauto]; eauto. Qed.

Theorem paco_unfold: forall (MON: monotone gf) r,
  paco gf r <1= gf (upaco gf r).
Proof. unfold monotone; intros; apply paco_observe in PR; destruct PR as []; eauto. Qed.

Theorem _paco_acc: forall
  l r (OBG: forall rr (INC: r <1== rr) (CIH: l <1== rr), l <1== paco gf rr),
  l <1== paco gf r.
Proof. unfold le1. eapply paco_acc. Qed.

Theorem _paco_mon: _monotone (paco gf).
Proof. apply monotone_eq. eapply paco_mon. Qed.

Theorem _paco_mult_strong: forall r,
  paco gf (upaco gf r) <1== paco gf r.
Proof. unfold le1. eapply paco_mult_strong. Qed.

Theorem _paco_fold: forall r,
  gf (upaco gf r) <1== paco gf r.
Proof. unfold le1. eapply paco_fold. Qed.

Theorem _paco_unfold: forall (MON: _monotone gf) r,
  paco gf r <1== gf (upaco gf r).
Proof.
  unfold le1. intro.
  eapply paco_unfold; apply monotone_eq; eauto.
Qed.

End Arg1.

#[export] Hint Unfold monotone : core.
#[export] Hint Resolve paco_fold : core.

Arguments paco_mon_gen        [ T0 ] gf gf' r r' x PR LEgf LEr.
Arguments paco_acc            [ T0 ] gf l r OBG x0 PR.
Arguments paco_mon            [ T0 ] gf x0 r r' IN LE.
Arguments paco_mult_strong    [ T0 ] gf r x0 PR.
Arguments paco_mult           [ T0 ] gf r x0 PR.
Arguments paco_fold           [ T0 ] gf r x0 PR.
Arguments paco_unfold         [ T0 ] gf MON r x0 PR.









Section PACO0.


(** ** Predicates of Arity 0
*)

Definition paco0(gf : rel0 -> rel0)(r: rel0) : rel0 :=
  @curry0 (paco (fun R0 => @uncurry0 (gf (@curry0 R0))) (@uncurry0 r)).

Definition upaco0(gf : rel0 -> rel0)(r: rel0) := paco0 gf r \0/ r.
Arguments paco0 : clear implicits.
Arguments upaco0 : clear implicits.
#[local] Hint Unfold upaco0 : core.

Definition monotone0 (gf: rel0 -> rel0) :=
  forall r r' (IN: gf r) (LE: r <0= r'), gf r'.

Definition _monotone0 (gf: rel0 -> rel0) :=
  forall r r'(LE: r <0= r'), gf r <0== gf r'.

Lemma monotone0_eq (gf: rel0 -> rel0) :
  monotone0 gf <-> _monotone0 gf.
Proof. unfold monotone0, _monotone0, le0. split; intros; eapply H; eassumption. Qed.

Lemma monotone0_map (gf: rel0 -> rel0)
      (MON: _monotone0 gf) :
  _monotone (fun R0 => @uncurry0 (gf (@curry0 R0))).
Proof.
  red; intros. apply uncurry_map0. apply MON; apply curry_map0; assumption.
Qed.

Lemma monotone0_compose (gf gf': rel0 -> rel0)
      (MON1: monotone0 gf)
      (MON2: monotone0 gf'):
  monotone0 (compose gf gf').
Proof.
  red; intros. eapply MON1. apply IN.
  intros. eapply MON2. apply PR. apply LE.
Qed.

Lemma monotone0_union (gf gf': rel0 -> rel0)
      (MON1: monotone0 gf)
      (MON2: monotone0 gf'):
  monotone0 (gf \1/ gf').
Proof.
  red; intros. destruct IN.
  - left. eapply MON1. apply H. apply LE.
  - right. eapply MON2. apply H. apply LE.
Qed.

Lemma _paco0_mon_gen (gf gf': rel0 -> rel0) r r'
    (LEgf: gf <1= gf')
    (LEr: r <0= r'):
  paco0 gf r <0== paco0 gf' r'.
Proof.
  apply curry_map0. red; intros. eapply paco_mon_gen. apply PR.
  - intros. apply LEgf, PR0.
  - intros. apply LEr, PR0.
Qed.

Lemma paco0_mon_gen (gf gf': rel0 -> rel0) r r'
    (REL: paco0 gf r)
    (LEgf: gf <1= gf')
    (LEr: r <0= r'):
  paco0 gf' r'.
Proof.
  eapply _paco0_mon_gen; [apply LEgf | apply LEr | apply REL].
Qed.

Lemma paco0_mon_bot (gf gf': rel0 -> rel0) r'
    (REL: paco0 gf bot0)
    (LEgf: gf <1= gf'):
  paco0 gf' r'.
Proof.
  eapply paco0_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Lemma upaco0_mon_gen (gf gf': rel0 -> rel0) r r'
    (REL: upaco0 gf r)
    (LEgf: gf <1= gf')
    (LEr: r <0= r'):
  upaco0 gf' r'.
Proof.
  destruct REL.
  - left. eapply paco0_mon_gen; [apply H | apply LEgf | apply LEr].
  - right. apply LEr, H.
Qed.

Lemma upaco0_mon_bot (gf gf': rel0 -> rel0) r'
    (REL: upaco0 gf bot0)
    (LEgf: gf <1= gf'):
  upaco0 gf' r'.
Proof.
  eapply upaco0_mon_gen; [apply REL | apply LEgf | intros; contradiction PR].
Qed.

Section Arg0.

Variable gf : rel0 -> rel0.
Arguments gf : clear implicits.

Theorem _paco0_mon: _monotone0 (paco0 gf).
Proof.
  red; intros. eapply curry_map0, _paco_mon; apply uncurry_map0; assumption.
Qed.

Theorem _paco0_acc: forall
  l r (OBG: forall rr (INC: r <0== rr) (CIH: l <0== rr), l <0== paco0 gf rr),
  l <0== paco0 gf r.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply _paco_acc. intros.
  apply uncurry_adjoint1_0 in INC. apply uncurry_adjoint1_0 in CIH.
  apply uncurry_adjoint2_0.
  eapply le0_trans. eapply (OBG _ INC CIH).
  apply curry_map0.
  apply _paco_mon; try apply le1_refl; apply curry_bij1_0.
Qed.

Theorem _paco0_mult_strong: forall r,
  paco0 gf (upaco0 gf r) <0== paco0 gf r.
Proof.
  intros. apply curry_map0.
  eapply le1_trans; [| eapply _paco_mult_strong].
  apply _paco_mon; intros [] H; apply H.
Qed.

Theorem _paco0_fold: forall r,
  gf (upaco0 gf r) <0== paco0 gf r.
Proof.
  intros. apply uncurry_adjoint1_0.
  eapply le1_trans; [| apply _paco_fold]. apply le1_refl.
Qed.

Theorem _paco0_unfold: forall (MON: _monotone0 gf) r,
  paco0 gf r <0== gf (upaco0 gf r).
Proof.
  intros. apply curry_adjoint2_0.
  eapply _paco_unfold; apply monotone0_map; assumption.
Qed.

Theorem paco0_acc: forall
  l r (OBG: forall rr (INC: r <0= rr) (CIH: l <0= rr), l <0= paco0 gf rr),
  l <0= paco0 gf r.
Proof.
  apply _paco0_acc.
Qed.

Theorem paco0_mon: monotone0 (paco0 gf).
Proof.
  apply monotone0_eq.
  apply _paco0_mon.
Qed.

Theorem upaco0_mon: monotone0 (upaco0 gf).
Proof.
  red; intros.
  destruct IN.
  - left. eapply paco0_mon. apply H. apply LE.
  - right. apply LE, H.
Qed.

Theorem paco0_mult_strong: forall r,
  paco0 gf (upaco0 gf r) <0= paco0 gf r.
Proof.
  apply _paco0_mult_strong.
Qed.

Corollary paco0_mult: forall r,
  paco0 gf (paco0 gf r) <0= paco0 gf r.
Proof. intros; eapply paco0_mult_strong, paco0_mon; [apply PR|..]; intros; left; assumption. Qed.

Theorem paco0_fold: forall r,
  gf (upaco0 gf r) <0= paco0 gf r.
Proof.
  apply _paco0_fold.
Qed.

Theorem paco0_unfold: forall (MON: monotone0 gf) r,
  paco0 gf r <0= gf (upaco0 gf r).
Proof.
  intro. eapply _paco0_unfold; apply monotone0_eq; assumption.
Qed.

End Arg0.

Arguments paco0_acc : clear implicits.
Arguments paco0_mon : clear implicits.
Arguments upaco0_mon : clear implicits.
Arguments paco0_mult_strong : clear implicits.
Arguments paco0_mult : clear implicits.
Arguments paco0_fold : clear implicits.
Arguments paco0_unfold : clear implicits.

Global Instance paco0_inst  (gf : rel0->_) r : paco_class (paco0 gf r) :=
{ pacoacc    := paco0_acc gf;
  pacomult   := paco0_mult gf;
  pacofold   := paco0_fold gf;
  pacounfold := paco0_unfold gf }.

End PACO0.

Global Opaque paco0.

#[export] Hint Unfold upaco0 : core.
#[export] Hint Resolve paco0_fold : core.
#[export] Hint Unfold monotone0 : core.
