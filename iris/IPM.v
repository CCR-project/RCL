Require Import Algebra Coqlib.
Require Import String.
Set Implicit Arguments.
Open Scope string_scope.
Open Scope list_scope.



From iris.bi Require Import derived_connectives updates.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
Require Export DisableSsreflect.
Arguments Z.of_nat: simpl nomatch.



Section LOGIC.

  Context `{M: MRAS.t}.

  Definition mPred := (MRAS.car -> Prop)%type.

  Record mProp :=
    mProp_intro {
        mProp_pred :> mPred;
        (* mProp_perm: forall r0 r1 (LE: r0 ≡ r1), mProp_pred r0 -> mProp_pred r1; *)
        mProp_mono :> Proper ((≼) ==> (impl)) mProp_pred;
      }.
  Arguments mProp_intro: clear implicits.

  Global Program Instance mProp_equiv: Proper (eq ==> (≡) ==> impl) mProp_pred.
  Next Obligation.
    ii. subst. eapply mProp_mono; et. rewrite H0. refl.
  Qed.

  Program Definition Sepconj (P Q: mProp): mProp :=
    mProp_intro (fun m => exists a b, m ≡ (a ⊕ b) /\ (P: mPred) a /\ (Q: mPred) b) _.
  Next Obligation.
    ii. des. subst. r in H. des; setoid_subst. esplits.
    { rewrite oplus_assoc. et. }
    { et. }
    { eapply mProp_mono; et. rr. et. }
  Qed.

  Program Definition Pure (P: Prop): mProp := mProp_intro (fun _ => P) _.

  Program Definition Ex {X: Type} (P: X -> mProp): mProp := mProp_intro (fun sm => exists x, (P x: mPred) sm) _.
  Next Obligation.
    ii. ss. des. esplits; et. eapply mProp_mono; et.
  Qed.

  Program Definition Univ {X: Type} (P: X -> mProp): mProp := mProp_intro (fun sm => forall x, (P x: mPred) sm) _.
  Next Obligation.
    ii. ss. des. esplits; et. eapply mProp_mono; et.
  Qed.

  Program Definition Own (m0: MRAS.car): mProp := mProp_intro (fun sm => m0 ≼ sm) _. (* sublist m0 sm. *)
  Next Obligation.
    ii. ss. etrans; et.
  Qed.

  Variant Entails (P Q : mProp) : Prop :=
    | entails_intro: (forall sm0, (P: mPred) sm0 -> (Q: mPred) sm0) -> Entails P Q
  .

  Program Instance Entails_PreOrder: PreOrder Entails.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. inv H. inv H0. econs; et. Qed.

  Program Definition Wand (P Q: mProp): mProp :=
    mProp_intro (fun sm => forall smp, (P: mPred) smp -> (Q: mPred) (sm ⊕ smp)) _
  .
  Next Obligation.
    ii. ss. eapply mProp_mono; [|eapply H0]; et. rewrite H. refl.
  Qed.

  Program Definition And (P Q : mProp) : mProp :=
    mProp_intro (fun sm0 => (P: mPred) sm0 /\ (Q: mPred) sm0) _
  .
  Next Obligation.
    ii. ss. des. esplits; eapply mProp_mono; et.
  Qed.

  Program Definition Or (P Q : mProp) : mProp :=
    mProp_intro (fun sm0 => (P: mPred) sm0 \/ (Q: mPred) sm0) _
  .
  Next Obligation.
    ii. ss. des. { left. eapply mProp_mono; et. } { right. eapply mProp_mono; et. }
  Qed.

  Program Definition Impl (P Q : mProp) : mProp :=
    mProp_intro (fun sm0 => ∀ sm1 (LE: sm0 ≼ sm1), (P: mPred) sm1 -> (Q: mPred) sm1) _
  .
  Next Obligation.
    ii. eapply H0; et. etrans; et.
  Qed.

  (*** Refining ***)
  Program Definition Refines (Q: mProp): mProp :=
    mProp_intro (fun tgt => exists src, (Q: mPred) src /\ (tgt ⊑ src)) _
  .
  Next Obligation.
    ii. ss. des. esplits; et. rewrite <- H. ss.
  Qed.

  Lemma ref_mono: forall P Q, Entails P Q -> Entails (Refines P) (Refines Q).
  Proof.
    unfold Refines. ii; ss. inv H. econs. ii; ss. des. esplits; eauto.
  Qed.

  Lemma ref_intro: forall P, Entails P (Refines P).
  Proof.
    unfold Refines.
    ii; ss. econs; ii; ss.
    esplits; eauto.
  Qed.

  Lemma ref_elim: forall P, Entails (Refines (Refines P)) (Refines P).
  Proof.
    unfold Refines.
    ii; ss. econs; ii; ss.
    des. esplits; eauto.
    etrans; et.
  Qed.

  (*** ref is like an update modality ***)
  Lemma ref_frame: forall P Q, Entails (Sepconj (Refines Q) P) (Refines (Sepconj Q P)).
  Proof.
    unfold Refines, Sepconj.
    ii; ss. econs; ii; ss.
    des. setoid_subst. exists (src ⊕ b). esplits; eauto.
    rewrite H2. refl.
  Qed.

  Definition Emp := Pure True.

  Theorem Refines_Absorbing: forall P, Entails (Sepconj Emp (Refines P)) (Refines P).
  Proof.
    unfold Sepconj, Pure, Refines.
    ii; ss. econs; ii; ss.
    des. setoid_subst. esplits; et. ii. etrans; revgoals; et.
    eapply included_ref. rr. esplits; et. rewrite oplus_comm; et.
  Qed.

  Theorem Emp_spec: forall P, Entails P Emp.
  Proof. ii. ss. Qed.

  Theorem adequacy: forall x y, Entails (Own x) (Refines (Own y)) <-> x ⊑ y.
  Proof.
    split; ii.
    - rr in H. inv H. exploit H0; ss. { refl. } intro T; des. etrans; et. eapply included_ref; et.
    - rr. econs. i; ss. rr in H0. des. setoid_subst. esplits. { rr. esplits; et. } rewrite H. refl.
  Qed.

  Lemma mProp_eta: ∀ x y, x.(mProp_pred) = y.(mProp_pred) -> x = y.
  Proof.
    destruct x, y; ss. i. dependent destruction H. f_equal. eapply proof_irr.
  Qed.

  Lemma equiv_entails: ∀ P Q, (P = Q) <-> Entails P Q ∧ Entails Q P.
  Proof.
    split; i.
    - subst; split; refl.
    - des. eapply mProp_eta. extensionality x. eapply Axioms.prop_ext. split; i; et.
      { eapply H; et. }
      { eapply H0; et. }
  Qed.



  Lemma Sep_mono: forall P P' Q Q', Entails P Q -> Entails P' Q' -> Entails (Sepconj P P') (Sepconj Q Q').
  Proof.
    unfold Sepconj. ii; ss. inv H. inv H0. econs; ii; ss. des. esplits; et.
  Qed.

  Lemma Sep_emp1: forall P, Entails P (Sepconj Emp P).
  Proof.
    unfold Sepconj, Emp. ii; ss. econs; ii; ss. des. esplits; et.
    { rewrite oplus_comm. rewrite eps_r. ss. }
  Qed.

  Lemma Sep_emp2: forall P, Entails (Sepconj Emp P) P.
  Proof.
    unfold Sepconj, Emp. econs; ii; ss. des.
    eapply mProp_mono; try apply H1.
    rewrite H.
    rr. exists a. rewrite oplus_comm; ss.
  Qed.

  Lemma Sep_comm: forall P Q, Entails (Sepconj P Q) (Sepconj Q P).
  Proof.
    unfold Sepconj, Emp. econs; ii; ss. des. esplits; revgoals; try eassumption. etrans; et.
    rewrite oplus_comm; ss.
  Qed.

  Lemma Sep_assoc: forall P Q R, Entails (Sepconj (Sepconj P Q) R) (Sepconj P (Sepconj Q R)).
  Proof.
    unfold Sepconj, Emp. econs; ii; ss. des. esplits; revgoals; try eassumption; try refl.
    rewrite H. rewrite H0.
    rewrite oplus_assoc; ss.
  Qed.

  Lemma Wand_intro_r: forall P Q R : mProp, Entails (Sepconj P Q) R -> Entails P (Wand Q R).
  Proof.
    unfold Sepconj, Wand. econs; ii; ss. inv H; ss. eapply H2; et.
  Qed.

  Lemma Wand_elim_l: forall P Q R : mProp, Entails P (Wand Q R) -> Entails (Sepconj P Q) R.
  Proof.
    unfold Sepconj, Wand. ii; ss. econs; ii; inv H; ss. des; setoid_subst. eapply H1; eauto.
  Qed.

  (* bi_persistently *)
  Program Definition Pers (P: mProp): mProp :=
    mProp_intro (fun sm => (P: mPred) (|sm|)) _
  .
  Next Obligation.
    ii; ss. eapply mProp_mono; [|et]. rewrite H. refl.
  Qed.

  Lemma Pers_mono: forall P Q, Entails P Q -> Entails (Pers P) (Pers Q).
  Proof.
    unfold Pers. ii. inv H; econs; ss. eauto.
  Qed.

  Lemma Pers_idemp_2: forall P, Entails (Pers P) (Pers (Pers P)).
  Proof.
    unfold Pers. ii; ss. econs; ss; ii.
    rewrite bar_idemp; ss.
  Qed.

  Lemma Pers_emp_2: Entails Emp (Pers Emp).
  Proof.
    unfold Pers, Pure. econs; ss; ii.
  Qed.

  Lemma Pers_and_2: forall P Q, Entails (And (Pers P) (Pers Q)) (Pers (And P Q)).
  Proof.
    unfold Pers, And. ii. ss.
  Qed.

  Lemma Pers_exists_1: forall A (Ψ: A -> mProp), Entails (Pers (Ex Ψ)) (Ex (Pers ∘ Ψ)).
  Proof.
    unfold Pers, Ex. ii. ss.
  Qed.

  Lemma Pers_and_sep_elim: forall P Q, Entails (And (Pers P) Q) (Sepconj P Q).
  Proof.
    unfold Pers, And, Sepconj. econs; ii; ss. des. esplits; eauto. i.
    rewrite oplus_comm.
    eapply MRAS.bar_intro.
  Qed.

  Theorem absorbing: ∀ P, Entails (Sepconj P (Pure True)) P.
  Proof.
    unfold Pers, And, Sepconj. econs; ii; ss. des.
    eapply mProp_mono; try eassumption.
    rewrite H. rr. esplits; et.
  Qed.

  Lemma Pers_Absorbing: forall P Q, Entails (Sepconj (Pers P) Q) (Pers P).
  Proof.
    i. etrans.
    2: { eapply absorbing. }
    eapply Sep_mono; try refl.
    { ii. rr. ss. }
  Qed.

  Global Instance mPred_Equiv : Equiv mProp := eq.
  Global Instance uPred_Dist : Dist mProp := (fun _ => (≡)).

  Theorem mProp_bi_mixin:
    BiMixin
      Entails Emp Pure And Or Impl
      (@Univ) (@Ex) Sepconj Wand
      Pers.
  Proof.
    econs; try (by typeclasses eauto).
    - eapply equiv_entails.
    - ii. rr. unfold Pure. eapply mProp_eta; ss. extensionality sm. eapply Axioms.prop_ext; ss.
    - ii. rr. unfold Univ. eapply mProp_eta; ss. extensionalities sm b. rewrite H. ss.
    - ii. rr. unfold Ex. eapply mProp_eta; ss. extensionalities sm. eapply Axioms.prop_ext. split; i; des; esplits.
      + rewrite <- H; et.
      + rewrite H; et.
    - ii. rr. ss.
    - ii. econs. ii; ss. eapply H; et. rr. ss.
    - ii. econs; ii; ss. des; ss.
    - ii. econs; ii; ss. des; ss.
    - ii. inv H. inv H0. econs; ii; ss. esplits; et.
    - ii. econs; ii; ss. et.
    - ii. econs; ii; ss. et.
    - ii. inv H. inv H0. econs; ii; ss. des; et.
    - ii. econs; ii; ss. eapply H. rr. esplits; et. eapply mProp_mono; et.
    - ii. econs; ii; ss. rr in H0. des. eapply H in H0. eapply H0; et. refl.
    - ii. econs; ii; ss. eapply H; et.
    - ii. econs; ii; ss.
    - ii. econs; ii; ss. rr; et.
    - ii. econs; ii; ss. rr in H0; des. eapply H; et.
    - eapply Sep_mono.
    - eapply Sep_emp1.
    - eapply Sep_emp2.
    - eapply Sep_comm.
    - eapply Sep_assoc.
    - eapply Wand_intro_r.
    - eapply Wand_elim_l.
    - eapply Pers_mono.
    - eapply Pers_idemp_2.
    - eapply Pers_emp_2.
    - eapply Pers_and_2.
    - eapply Pers_exists_1.
    - eapply Pers_Absorbing.
    - eapply Pers_and_sep_elim.
  Qed.

  Program Definition Later (P: mProp): mProp := mProp_intro P _.
  Next Obligation. eapply mProp_mono; eauto. Qed.

  Theorem mProp_bi_later_mixin:
    BiLaterMixin
      Entails Pure Or Impl
      (@Univ) (@Ex) Sepconj Pers Later.
  Proof.
    econs.
    - ii. rr in H. subst. ss.
    - ii. unfold Later in *; ss. econs; ii; ss. eapply H; et.
    - ii. unfold Later in *; ss.
    - ii. unfold Later in *; ss.
    - ii. unfold Later in *; ss. econs; ii; ss. et.
    - ii. unfold Later in *; ss.
    - ii. unfold Later in *; ss.
    - ii. unfold Later in *; ss.
    - ii. unfold Later in *; ss.
    - ii. unfold Later in *; ss. econs; ii; ss. right. ii. eapply mProp_mono; et.
  Qed.

  Canonical Structure mPropp: bi :=
    {| bi_bi_mixin := mProp_bi_mixin;
       bi_bi_later_mixin := mProp_bi_later_mixin |}.

  Global Program Instance mProp_Absorbing: ∀ (P: mProp), Absorbing P.
  Next Obligation.
    i. unfold bi_absorbingly. iIntros "[A B]". iApply absorbing; eauto. iSplit; ss.
  Qed.

  Global Program Instance mProp_Affine: BiAffine mPropp.
  Next Obligation.
    ii; ss.
  Qed.

  Theorem mProp_bupd_mixin: BiBUpdMixin mPropp Refines.
  Proof.
    econs.
    - ii; ss. rr. rr in H. subst; ss.
    - eapply ref_intro.
    - eapply ref_mono.
    - eapply ref_elim.
    - i. eapply ref_frame.
  Qed.

  Global Instance mProp_bi_bupd: BiBUpd mPropp :=
    {| bi_bupd_mixin := mProp_bupd_mixin |}.

  Context `{S: CM.t, EF: @EndoFun.t _ S}.

  Program Definition MyMod (s0: CM.car) (P: mProp): mProp :=
    mProp_intro (fun sm => exists sm0, (EndoFun.morph s0 sm0) ≼ sm /\ (P: mPred) sm0) _.
  Next Obligation.
    ii. des. esplits; et. etrans; et.
  Qed.

  Lemma mymod_mono: forall s P Q, (P ⊢ Q) -> ((MyMod s P) ⊢ (MyMod s Q)).
  Proof.
    ii. econs; ii; ss. des. esplits; et. eapply H; et.
  Qed.

  Lemma mymod_idem: forall s0 s1 P, (MyMod s1 (MyMod s0 P)) ⊣⊢ (MyMod (s0 ⋅ s1) P).
  Proof.
    ii. unfold equiv. unfold mPred_Equiv. eapply mProp_eta. extensionalities sm. eapply Axioms.prop_ext.
    split; ii; ss; des.
    - esplits; et. etrans; et. rewrite <- EndoFun.morph_idem. rewrite EndoFun.morph_mono; et. refl.
    - rewrite <- EndoFun.morph_idem in H. esplits; et. refl.
  Qed.

  Lemma mymod_sep: forall s P Q, (MyMod s (P ∗ Q)) ⊣⊢ (MyMod s P) ∗ (MyMod s Q).
  Proof.
    ii. unfold equiv. unfold mPred_Equiv. eapply mProp_eta. extensionalities sm. eapply Axioms.prop_ext.
    unfold bi_sep. cbn. split; ii; ss; des; subst.
    - rr in H. des. subst.
      eexists (EndoFun.morph s a ⋅ ctx), (EndoFun.morph s b). esplits.
      { setoid_subst. rewrite <- EndoFun.morph_add. r_solve. }
      { r. et. }
      { ss. }
      { refl. }
      { ss. }
    - setoid_subst. esplits; eauto. rewrite <- EndoFun.morph_add. rewrite H0. rewrite H1. refl.
  Qed.

  Lemma mymod_pers_commute: forall s P, MyMod s (<pers> P) ⊢ <pers> (MyMod s P).
  Proof.
    unfold MyMod, bi_persistently. econs; ii; ss. des. esplits; et. rewrite EndoFun.morph_core.
    eapply Mod.core_extends. et.
  Qed.

  (* Lemma mymod_ref_commute: forall s P, MyMod s (bupd P) ⊢ |==> (MyMod s P). *)
  (* Proof. *)
  (*   unfold MyMod, bi_persistently. econs; ii; ss. des. esplits. *)
  (*   3: { rewrite <- H. eapply EndoFun.morph_ref. eauto. } *)
  (*   { refl. } *)
  (*   { ss. } *)
  (* Qed. *)

  Lemma mymod_own: forall s m, MyMod s (Own m) ⊣⊢ Own (EndoFun.morph s m).
  Proof.
    ii. eapply equiv_entails. split.
    - econs; ii. rr in H. cbn. des. rr in H0. des. setoid_subst. rewrite <- EndoFun.morph_add in H.
      etrans; et. r; et.
    - econs; ii. rr in H. cbn. des. subst. esplits; try refl. r; et.
  Qed.

  Lemma mymod_exists_commute: forall s X P, MyMod s (∃ (x: X), P x) ⊣⊢ ∃ x, (MyMod s (P x)).
  Proof.
    unfold MyMod, bi_persistently, bi_exist. ii; ss. unfold Ex. eapply equiv_entails.
    ss. splits; econs; ii; ss; des; et.
  Qed.

  Lemma mymod_unit: ∀ P, MyMod ε P ⊣⊢ P.
  Proof.
    ii. rr. eapply mProp_eta. extensionalities sm. ss. eapply Axioms.prop_ext. split; i.
    { des. rewrite EndoFun.morph_unit in H. eapply mProp_mono; et. }
    { esplits; et. rewrite EndoFun.morph_unit. refl. }
  Qed.

  Corollary mymod_wand: forall s P Q, (MyMod s (P -∗ Q)) ⊢ (MyMod s P -∗ MyMod s Q).
  Proof.
    iIntros (???) "A B".
    iDestruct (mymod_sep with "[A B]") as "A"; iFrame.
    iStopProof.
    eapply mymod_mono.
    iIntros "[A B]". iApply "B". eauto.
    (* unfold bi_wand. cbn. ii; ss; des; subst. *)
    (* - rr in H. des. subst. *)
    (*   esplits; et. rewrite <- EndoFun.morph_add. *)
    (*   eapply CM.add_extends; ss. r; et. *)
  Qed.

  Program Definition MyMod2 (s0: CM.car) (P: mProp): mProp :=
    mProp_intro (fun sm => (P: mPred) (EndoFun.morph s0 sm)) _.
  Next Obligation.
    ii. rr in H. des. setoid_subst. rewrite <- EndoFun.morph_add. eapply mProp_mono; et. r; et.
  Qed.

  Lemma mymod_emp s : (emp ⊢ MyMod s emp)%I.
  Proof.
    unfold MyMod. econs; ii; ss. rr in H. exists ε. esplits; et. rewrite EndoFun.morph_unit2.
    exists sm0. rewrite oplus_comm. rewrite eps_r. ss.
  Qed.

  Lemma mymod2_emp s : (emp ⊢ MyMod2 s emp)%I.
  Proof.
    unfold MyMod2. econs; ii; ss.
  Qed.

  Theorem mymod2_adj0: ∀ s P Q, (P ⊢ MyMod2 s Q) -> (MyMod s P ⊢ Q).
  Proof.
    unfold MyMod, MyMod2, bi_entails. ss. econs; ii; inv H; ss; des.
    - exploit H1; et. intro T. eapply mProp_mono; et.
  Qed.

  Theorem mymod2_adj1: ∀ s P Q, (MyMod s P ⊢ Q) -> (P ⊢ MyMod2 s Q).
  Proof.
    unfold MyMod, MyMod2, bi_entails. ss. econs; ii; inv H; ss; des.
    - exploit H1; et. esplits; et. refl.
  Qed.

  Corollary mymod_mymod2: ∀ s P, MyMod s (MyMod2 s P) ⊢ P.
  Proof.
    i. iIntros "H". iApply mymod2_adj0; [|et]. ss.
  Qed.

  Corollary mymod2_mymod: ∀ s P, P ⊢ MyMod2 s (MyMod s P).
  Proof.
    i. iIntros "H". iApply mymod2_adj1; [|iAssumption]. ss.
  Qed.

  Program Definition RevPers (P: mProp): mProp :=
    mProp_intro (fun r => ∃ r', Mod.core r' ≼ r ∧ (P: mPred) r') _
  .
  Next Obligation.
    ii. des. esplits; et. etrans; et.
  Qed.

  Goal ∀ (P Q: mProp), (P ⊢ Pers Q) -> RevPers P ⊢ Q.
  Proof.
    unfold Pers, RevPers in *. econs. ss. inv H. ss.
    ii. des. exploit H0; et. i. eapply mProp_mono; et.
  Qed.

  Lemma mymod2_mono: ∀ s P Q, (P ⊢ Q) -> (MyMod2 s P ⊢ MyMod2 s Q).
  Proof.
    unfold MyMod2. i. econs; ii; ss.
    { eapply H; et. }
  Qed.

  Lemma mymod2_unit: ∀ P, MyMod2 ε P ⊣⊢ P.
  Proof.
    i. iIntros. iSplit; iIntros "H".
    - iStopProof.
      unfold MyMod2. econs; ii; ss. eapply mProp_mono; et. rewrite EndoFun.morph_unit. refl.
    - iApply mymod2_adj1; [|iAssumption]. iIntros "H". iApply mymod_unit; ss.
  Qed.

  Class MyModAction s (P Q : mProp) := maybe_into_laterN : P ⊢ MyMod s Q.
  Global Instance MyModAction_default s (P : mProp): MyModAction s (MyMod s P) P.
    econs. ii. ss.
  Defined.
  (* Global Arguments MaybeIntoLaterN {_} _ _%nat_scope _%I _%I. *)
  (* Global Arguments maybe_into_laterN {_} _ _%nat_scope _%I _%I {_}. *)
  (* Global Hint Mode MaybeIntoLaterN + + + - - : typeclass_instances. *)

  Lemma modality_mymod_mixin s :
    modality_mixin (MyMod s) (MIEnvClear) (MIEnvTransform (MyModAction s)).
  Proof.
    econs; ss.
    (* - i. iIntros "H". iApply H. ss. *)
    - eapply mymod_emp.
    - i. eapply mymod_mono; et.
    - i. iIntros "[A B]". iApply mymod_sep; et. iFrame.
  Qed.

  Global Program Instance mymod_into_sep s P Q: IntoSep (MyMod s (P ∗ Q)%I) (MyMod s P) (MyMod s Q).
  Next Obligation.
    i. iIntros "H". iApply mymod_sep; ss.
  Qed.

  Global Program Instance mymod_from_sep s P Q: FromSep (MyMod s (P ∗ Q)%I) (MyMod s P) (MyMod s Q).
  Next Obligation.
    i. iIntros "H". iApply mymod_sep; ss.
  Qed.

  Lemma modality_mymod2_mixin s :
    modality_mixin (MyMod2 s) (MIEnvClear) (MIEnvTransform (λ P Q, MyMod s P ≡ Q)).
  Proof.
    econs; ss.
    - i. iIntros "H". iApply mymod2_adj1; [|iAssumption]. iIntros "H". iApply H. ss.
    - i. eapply mymod2_mono; et.
    - i. iIntros "[A B]". iApply mymod2_adj1; [|et].
      2: { instantiate (1:=(_ ∗ _)%I). iSplitL "A"; iAssumption. }
      iIntros "[A B]". iDestruct (mymod_mymod2 with "A") as "A". iDestruct (mymod_mymod2 with "B") as "B". iFrame.
  Qed.

  Definition modality_mymod s := Modality _ (modality_mymod_mixin s).
  Definition modality_mymod2 s := Modality _ (modality_mymod2_mixin s).

  Definition Refines2 (P: mProp): mProp := (∀ s, MyMod2 s (bupd (MyMod s P)))%I.

  Theorem Refines2_spec: ∀ P Q, (P ⊢ Refines2 Q) <-> (∀ s, MyMod s P ⊢ Refines (MyMod s Q)).
  Proof.
    unfold Refines2. i. split; i.
    - iIntros "H".
      assert(T: ∀ s, P -∗ MyMod2 s (Refines (MyMod s Q))).
      { i. iIntros "A". iDestruct (H with "A") as "A". eauto. }
      clear H.
      iDestruct (@mymod2_adj0) as "T".
      { eauto. }
      iApply "T". eauto.
    - iIntros "A". iIntros (s). iApply mymod2_adj1; eauto.
  Qed.

  Lemma ref2_mono: forall P Q, Entails P Q -> Entails (Refines2 P) (Refines2 Q).
  Proof.
    unfold Refines2. ii; ss.
    iIntros "H". iIntros (s). iApply mymod2_mono; [|et].
    iIntros. iApply ref_mono; [|et]. eapply mymod_mono; et.
  Qed.

  Lemma ref2_intro: forall P, Entails P (Refines2 P).
  Proof.
    unfold Refines2.
    ii; ss.
    iIntros "H". iIntros (s).
    iApply mymod2_adj1; [|iAssumption].
    iIntros "H". iApply ref_intro. ss.
  Qed.

  Lemma ref2_elim: forall P, Entails (Refines2 (Refines2 P)) (Refines2 P).
  Proof.
    unfold Refines2.
    ii; ss. iIntros "H". iIntros (s).
    {
      iSpecialize ("H" $! s).
      iApply mymod2_mono; [|iAssumption].
      iIntros "H". iMod "H". iApply mymod2_adj0; [|et].
      iIntros "H". eauto.
    }
    (* M |=> W M |=> W P *)
    (* --------------- *)
    (* M |=> W P *)
  Qed.

  Lemma ref2_frame: forall P Q, Entails ((Refines2 Q) ∗ P)%I (Refines2 (Q ∗ P)%I).
  Proof.
    unfold Refines2.
    ii; ss. iIntros "[A B]". iIntros (s).
    {
      iSpecialize ("A" $! s).
      iApply mymod2_adj1.
      2: { instantiate (1:= (_ ∗ _)%I). iSplitL "A"; iAssumption. }
      iIntros "[A B]".
      iDestruct (mymod_mymod2 with "A") as "A".
      iMod "A". iModIntro. iSplitL "A"; et.
    }
  Qed.

  Lemma mymod_idem2: forall s0 s1 P, (MyMod2 s1 (MyMod2 s0 P)) ⊣⊢ (MyMod2 (s0 ⋅ s1) P).
  Proof.
    ii. unfold equiv. unfold mPred_Equiv. eapply mProp_eta. extensionalities sm. eapply Axioms.prop_ext.
    split; ii; ss; des.
    - rewrite EndoFun.morph_idem in H. rewrite oplus_comm. ss.
    - rewrite EndoFun.morph_idem. rewrite oplus_comm. ss.
  Qed.

  Lemma mymod_ref2_commute: forall s P, MyMod s (Refines2 P) ⊢ Refines2 (MyMod s P).
  Proof.
    i. unfold Refines2. iIntros "H". iIntros (s').
    - iApply mymod2_adj1; [|iAssumption]. iIntros "H".
      iDestruct (mymod_idem with "H") as "H".
      iDestruct (mymod_mono with "H") as "H".
      { iIntros "H". iSpecialize ("H" $! (s ⋅ s')). iAssumption. }
      iDestruct (mymod_mymod2 with "H") as "H".
      iMod "H". iModIntro. iApply mymod_idem. ss.
(*
W M |=> W P
--------------
M |=> W M P
*)
  Qed.

  Corollary Refines_Refines2_sub: ∀ P, (Refines2 P ⊢ |==> P)%I.
  Proof.
    unfold Refines2. i. iIntros "H". iSpecialize ("H" $! ε).
    iApply mymod2_unit. iApply mymod2_mono; [|et]. iIntros "H".
    iMod "H". iModIntro.
    iApply mymod_unit. ss.
  Qed.

  Definition CondRefines (s: S) (P Q: mProp): mProp := (∀ b, MyMod b P ==∗ (MyMod (s ⋅ b) Q))%I.
  Theorem CondRefines_tcomp: ∀ s P0 Q0 P1 Q1, CondRefines s P0 Q0 -∗ CondRefines s P1 Q1 -∗ CondRefines s (P0 ∗ P1) (Q0 ∗ Q1).
  Proof.
    i. unfold CondRefines.
    iIntros "A B" (b) "C".
    iDestruct (mymod_sep with "C") as "[C D]".
    iSpecialize ("A" with "C"). iMod "A".
    iSpecialize ("B" with "D"). iMod "B".
    iModIntro. iApply mymod_sep; iFrame.
  Qed.

  Lemma mymod_equiv: forall s0 s1 P, s0 ≡ s1 -> ((MyMod s0 P) ⊢ (MyMod s1 P)).
  Proof.
    ii. econs; ii; ss. des. esplits; et. rewrite <- H. ss.
  Qed.

  Theorem CondRefines_vcomp: ∀ s0 s1 P Q R, CondRefines s0 P Q -∗ CondRefines s1 Q R -∗ CondRefines (s0 ⋅ s1) P R.
  Proof.
    i. unfold CondRefines.
    iIntros "A B" (b) "C".
    iSpecialize ("A" with "C"). iMod "A".
    iSpecialize ("B" with "A"). iMod "B".
    iModIntro. iApply mymod_equiv.
    2: { iApply mymod_mono; et. }
    rewrite oplus_comm. rewrite <- ! oplus_assoc. f_equiv. rewrite oplus_comm. refl.
  Qed.

  Definition LCondRefines (s: S) (S0 T0 S1: mProp): mProp := (T0 -∗ CondRefines s S0 S1)%I.
  Lemma LCondRefines_vs: ∀ s S0 T0 S1, (LCondRefines s S0 T0 S1 ⊣⊢ (∀ b, (MyMod b S0 ∗ T0) ==∗ (MyMod (s ⋅ b) S1))).
  Proof.
    i. iSplit; iIntros "A".
    - iIntros (b) "[B C]". iSpecialize ("A" with "C"). iSpecialize ("A" $! b with "B"). ss.
    - iIntros "B" (b) "C". iSpecialize ("A" $! b with "[B C]"); iFrame.
  Qed.

  Theorem LCondRefines_tcomp: ∀ s P0 Q0 P1 Q1 R0 R1,
      LCondRefines s P0 Q0 R0 -∗ LCondRefines s P1 Q1 R1 -∗ LCondRefines s (P0 ∗ P1) (Q0 ∗ Q1) (R0 ∗ R1).
  Proof.
    i. unfold LCondRefines.
    iIntros "A B [C D]". iSpecialize ("A" with "C"). iSpecialize ("B" with "D").
    iApply (CondRefines_tcomp with "[A] [B]"); iFrame.
  Qed.

  Theorem LCondRefines_hcomp: ∀ s0 s1 T0 T1 S0 S1 S2,
      LCondRefines s0 S0 T0 S1 -∗ LCondRefines s1 S1 T1 S2 -∗ LCondRefines (s0 ⋅ s1) S0 (T0 ∗ T1) S2.
  Proof.
    i. unfold LCondRefines.
    iIntros "A B [C D]". iSpecialize ("A" with "C"). iSpecialize ("B" with "D").
    iApply (CondRefines_vcomp with "[A] [B]"); iFrame.
  Qed.

  Theorem LCondRefines_vcomp: ∀ s P0 P1 Q R0 R1,
      CondRefines ε P1 P0 -∗ CondRefines ε R0 R1 -∗
      LCondRefines s P0 Q R0 -∗ LCondRefines s P1 Q R1.
  Proof.
    i. unfold LCondRefines.
    iIntros "A B C D". iSpecialize ("C" with "D").
    iDestruct (CondRefines_vcomp with "[A] [C]") as "A"; eauto.
    iDestruct (CondRefines_vcomp with "[A] [B]") as "B"; eauto.
    iIntros (b) "A". iSpecialize ("B" $! (b) with "A").
    iMod "B". iModIntro.
    iApply mymod_equiv; [|iAssumption].
    rewrite eps_r. rewrite eps_rl. refl.
  Qed.

  Theorem mProp_bupd_mixin2: BiBUpdMixin mPropp Refines2.
  Proof.
    econs.
    - ii; ss. rr. rr in H. subst; ss.
    - eapply ref2_intro.
    - eapply ref2_mono.
    - eapply ref2_elim.
    - i. eapply ref2_frame.
  Qed.

  Global Instance mProp_bi_bupd2: BiBUpd mPropp :=
    {| bi_bupd_mixin := mProp_bupd_mixin2 |}.


End LOGIC.
