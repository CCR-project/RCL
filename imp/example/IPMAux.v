Require Import Coqlib.
Require Export sflib.
Require Export AList.
Require Import Skeleton.
Require Import Algebra.
Require Import ModSem Mod ModSemFacts ModFacts.
Require Import HTactics.
Require Import String.

Require Import IPM.

Set Implicit Arguments.

Section AUX.
  Context `{MRAS.t}.

  Global Program Instance Own_Proper: Proper ((≡) ==> (≡)) Own.
  Next Obligation.
    ii. rr. unfold Own. eapply mProp_eta; ss. extensionality sm.
    eapply Axioms.prop_ext. split; i; setoid_subst; ss.
  Qed.

  Lemma core_pers: ∀ a (PERS: a ≡ |a| ), Own a -∗ □ (Own a).
  Proof.
    i. econs. ii; ss. rr. esplits; ss. rr. rr in H0. des.
    esplits; ss. rewrite <- H0. rewrite bar_oplus. erewrite PERS at 1. refl.
  Qed.

End AUX.

Class IsOp {A : MRAS.t} (a b1 b2 : A) := is_op : a = b1 ⊕ b2.
Global Arguments is_op {_} _ _ _ {_}.
Global Hint Mode IsOp + - - - : typeclass_instances.

Global Instance is_op_op {A : MRAS.t} (a b : A) : IsOp (a ⊕ b) a b | 100.
Proof. by rewrite /IsOp. Qed.

Class IsOp' {A : MRAS.t} (a b1 b2 : A) := is_op' :> IsOp a b1 b2.
Global Hint Mode IsOp' + ! - - : typeclass_instances.
Global Hint Mode IsOp' + - ! ! : typeclass_instances.

Class IsOp'LR {A : MRAS.t} (a b1 b2 : A) := is_op_lr : IsOp a b1 b2.
Existing Instance is_op_lr | 0.
Global Hint Mode IsOp'LR + ! - - : typeclass_instances.
Global Instance is_op_lr_op {A : MRAS.t} (a b : A) : IsOp'LR (a ⊕ b) a b | 0.
Proof. by rewrite /IsOp'LR /IsOp. Qed.

#[export] Hint Unfold bi_entails bi_sep bi_and bi_or bi_wand bupd bi_bupd_bupd: iprop.

Section class_instances.
  Context `{Σ: MRAS.t}.

  Global Instance from_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 →
    FromSep (Own a) (Own b1) (Own b2).
  Proof.
    ii. inv H. red. rr.
    econs. ii. ss. rr in H. des. setoid_subst. rewrite H0. rewrite H1. refl.
  Qed.

  Global Instance into_and_own p (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoAnd p (Own a) (Own b1) (Own b2).
  Proof.
    ii. apply bi.intuitionistically_if_mono. inv H.
    econs. ii. ss. rr in H. des. setoid_subst. rr. esplits; ss.
    { exists (b2 ⊕ ctx). r_solve. }
    { exists (b1 ⊕ ctx). r_solve. }
  Qed.

  Global Instance into_sep_own (a b1 b2 : Σ) :
    IsOp a b1 b2 → IntoSep (Own a) (Own b1) (Own b2).
  Proof.
    ii. red. inv H.
    econs. ii. ss. rr in H. des. setoid_subst. rr. esplits; revgoals.
    { s; refl. }
    { exists (ctx). r_solve. }
    r_solve.
  Qed.

End class_instances.


Require Import WrapModSem WrapMod.

Section AUX.

  Context `{SK: Sk.ld}.

  Let mod_mras: MRAS.t := (MRA_to_MRAS (@Mod_MRA SK)).
  Opaque mod_mras.

  Definition OwnM (m: Mod.t) : (@mProp mod_mras) := Own (m: (mod_mras).(MRAS.car)).

  Global Program Instance OwnM_Proper0: Proper ((@equiv _ mod_mras.(MRAS.equiv)) ==> (≡)) OwnM.
  Next Obligation.
    ii. unfold OwnM. rewrite H. ss.
  Qed.

  Global Program Instance OwnM_Proper: Proper ((≡@{Mod.t}) ==> (≡)) OwnM.
  Next Obligation.
    ii. eapply OwnM_Proper0. setoid_subst. refl.
  Qed.

  Global Instance from_sep_ownM (a b1 b2 : mod_mras) :
    IsOp a b1 b2 →
    FromSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. unfold OwnM. inv H.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iApply "H".
  Qed.

  Global Instance into_and_ownM p (a b1 b2 : mod_mras) :
    IsOp a b1 b2 → IntoAnd p (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. apply bi.intuitionistically_if_mono. inv H.
    unfold OwnM. iIntros "[H1 H2]". iSplit.
    { iApply "H1". }
    { iApply "H2". }
  Qed.

  Global Instance into_sep_ownM (a b1 b2 : mod_mras) :
    IsOp a b1 b2 → IntoSep (OwnM a) (OwnM b1) (OwnM b2).
  Proof.
    ii. red. inv H. unfold OwnM.
    iIntros "[H1 H2]". iSplitL "H1"; iFrame.
  Qed.

  Lemma OwnM_persistent
        (m: Mod.t)
    :
    (OwnM m) -∗ (OwnM m ∗ □ OwnM ( | m | )).
  Proof.
    iIntros "A".
    assert(G:=@MRAS.bar_intro mod_mras m).
    iAssert (OwnM (m ⊕ ( |m| ))) with "[A]" as "[A B]".
    { iStopProof. rr. econs. ii. erewrite OwnM_Proper0; et. }
    iFrame.
    iApply core_pers; ss.
    assert(U:=@bar_idemp _ _ _ _ _ mod_mras.(MRAS.bar_facts) m).
    sym; ss.
  Qed.

End AUX.
