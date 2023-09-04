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

  Context `{CM: CM.t} `{W: !WA.t}.

  Program Definition Wrap (s0: CM.car) (P: mProp): mProp :=
    mProp_intro (fun sm => exists sm0, (𝑤_{s0} sm0) ≼ sm /\ (P: mPred) sm0) _.
  Next Obligation.
    ii. des. esplits; et. etrans; et.
  Qed.

  Notation "𝑊_{ a } b" := (Wrap a b) (at level 50).

  Lemma wrap_mono: forall s P Q, (P ⊢ Q) -> 𝑊_{s} P ⊢ 𝑊_{s} Q.
  Proof.
    ii. econs; ii; ss. des. esplits; et. eapply H; et.
  Qed.

  Lemma wrap_idem: forall `{!WA.Idem} s0 s1 P, (𝑊_{s1} (𝑊_{s0} P)) ⊣⊢ (𝑊_{s0 ⊕ s1} P).
  Proof.
    ii. unfold equiv. unfold mPred_Equiv. eapply mProp_eta. extensionalities sm. eapply Axioms.prop_ext.
    split; ii; ss; des.
    - esplits; et. etrans; et. rewrite <- WA.morph_idem. rewrite WA.morph_mono; et. refl.
    - rewrite <- WA.morph_idem in H0. esplits; et. refl.
  Qed.

  Lemma wrap_sep: forall s P Q, (𝑊_{s} (P ∗ Q)) ⊣⊢ (𝑊_{s} P) ∗ (𝑊_{s} Q).
  Proof.
    ii. unfold equiv. unfold mPred_Equiv. eapply mProp_eta. extensionalities sm. eapply Axioms.prop_ext.
    unfold bi_sep. cbn. split; ii; ss; des; subst.
    - rr in H. des. subst.
      eexists (𝑤_{s} a ⊕ ctx), (𝑤_{s} b). esplits.
      { setoid_subst. rewrite <- ! WA.morph_oplus. r_solve. }
      { r. et. }
      { ss. }
      { refl. }
      { ss. }
    - setoid_subst. esplits; eauto. rewrite <- WA.morph_oplus. rewrite H0. rewrite H1. refl.
  Qed.

  Lemma wrap_own: forall s m, 𝑊_{s} (Own m) ⊣⊢ Own (𝑤_{s} m).
  Proof.
    ii. eapply equiv_entails. split.
    - econs; ii. rr in H. cbn. des. rr in H0. des. setoid_subst.
      rewrite <- WA.morph_oplus in H.
      etrans; et. r; et.
    - econs; ii. rr in H. cbn. des. subst. esplits; try refl. r; et.
  Qed.

  Lemma wrap_exists_commute: forall s X P, 𝑊_{s} (∃ (x: X), P x) ⊣⊢ ∃ x, (𝑊_{s} (P x)).
  Proof.
    unfold Wrap, bi_persistently, bi_exist. ii; ss. unfold Ex. eapply equiv_entails.
    ss. splits; econs; ii; ss; des; et.
  Qed.

  Lemma wrap_unit: ∀ P, 𝑊_{ε} P ⊣⊢ P.
  Proof.
    ii. rr. eapply mProp_eta. extensionalities sm. ss. eapply Axioms.prop_ext. split; i.
    { des. rewrite WA.morph_unit in H. eapply mProp_mono; et. }
    { esplits; et. rewrite WA.morph_unit. refl. }
  Qed.

  Corollary wrap_wand: forall s P Q, (𝑊_{s} (P -∗ Q)) ⊢ (𝑊_{s} P -∗ 𝑊_{s} Q).
  Proof.
    iIntros (???) "A B".
    iDestruct (wrap_sep with "[A B]") as "A"; iFrame.
    iStopProof.
    eapply wrap_mono.
    iIntros "[A B]". iApply "B". eauto.
  Qed.

  Program Definition Wrap2 (s0: CM.car) (P: mProp): mProp :=
    mProp_intro (fun sm => (P: mPred) (𝑤_{s0} sm)) _.
  Next Obligation.
    ii. rr in H. des. setoid_subst. rewrite <- WA.morph_oplus. eapply mProp_mono; et. r; et.
  Qed.

  Notation "𝑀_{ a } b" := (Wrap2 a b) (at level 50).

  Lemma wrap_emp s : (emp ⊢ Wrap s emp)%I.
  Proof.
    unfold Wrap. econs; ii; ss. rr in H. exists ε. esplits; et. rewrite WA.morph_unit2.
    exists sm0. rewrite oplus_comm. rewrite eps_r. ss.
  Qed.

  Lemma wrap2_emp s : (emp ⊢ 𝑀_{s} emp)%I.
  Proof.
    unfold Wrap2. econs; ii; ss.
  Qed.

  Theorem wrap2_adj0: ∀ s P Q, (P ⊢ 𝑀_{s} Q) -> (𝑊_{s} P ⊢ Q).
  Proof.
    unfold Wrap, Wrap2, bi_entails. ss. econs; ii; inv H; ss; des.
    - exploit H1; et. intro T. eapply mProp_mono; et.
  Qed.

  Theorem wrap2_adj1: ∀ s P Q, (𝑊_{s} P ⊢ Q) -> (P ⊢ 𝑀_{s} Q).
  Proof.
    unfold Wrap, Wrap2, bi_entails. ss. econs; ii; inv H; ss; des.
    - exploit H1; et. esplits; et. refl.
  Qed.

  Corollary wrap_wrap2: ∀ s P, 𝑊_{s} (𝑀_{s} P) ⊢ P.
  Proof.
    i. iIntros "H". iApply wrap2_adj0; [|et]. ss.
  Qed.

  Corollary wrap2_wrap: ∀ s P, P ⊢ 𝑀_{s} (𝑊_{s} P).
  Proof.
    i. iIntros "H". iApply wrap2_adj1; [|iAssumption]. ss.
  Qed.

  Lemma wrap2_mono: ∀ s P Q, (P ⊢ Q) -> (𝑀_{s} P ⊢ 𝑀_{s} Q).
  Proof.
    unfold Wrap2. i. econs; ii; ss.
    { eapply H; et. }
  Qed.

  Lemma wrap2_unit: ∀ P, 𝑀_{ε} P ⊣⊢ P.
  Proof.
    i. iIntros. iSplit; iIntros "H".
    - iStopProof.
      unfold Wrap2. econs; ii; ss. eapply mProp_mono; et. rewrite WA.morph_unit. refl.
    - iApply wrap2_adj1; [|iAssumption]. iIntros "H". iApply wrap_unit; ss.
  Qed.

  Class WrapAction s (P Q : mProp) := maybe_into_laterN : P ⊢ Wrap s Q.
  Global Instance WrapAction_default s (P : mProp): WrapAction s (Wrap s P) P.
    econs. ii. ss.
  Defined.

  Lemma modality_wrap_mixin s :
    modality_mixin (Wrap s) (MIEnvClear) (MIEnvTransform (WrapAction s)).
  Proof.
    econs; ss.
    (* - i. iIntros "H". iApply H. ss. *)
    - eapply wrap_emp.
    - i. eapply wrap_mono; et.
    - i. iIntros "[A B]". iApply wrap_sep; et. iFrame.
  Qed.

  Global Program Instance wrap_into_sep s P Q: IntoSep (𝑊_{s} (P ∗ Q)%I) (𝑊_{s} P) (𝑊_{s} Q).
  Next Obligation.
    i. iIntros "H". iApply wrap_sep; ss.
  Qed.

  Global Program Instance wrap_from_sep s P Q: FromSep (𝑊_{s} (P ∗ Q)%I) (𝑊_{s} P) (𝑊_{s} Q).
  Next Obligation.
    i. iIntros "H". iApply wrap_sep; ss.
  Qed.

  Lemma modality_wrap2_mixin s :
    modality_mixin (Wrap2 s) (MIEnvClear) (MIEnvTransform (λ P Q, Wrap s P ≡ Q)).
  Proof.
    econs; ss.
    - i. iIntros "H". iApply wrap2_adj1; [|iAssumption]. iIntros "H". iApply H. ss.
    - i. eapply wrap2_mono; et.
    - i. iIntros "[A B]". iApply wrap2_adj1; [|et].
      2: { instantiate (1:=(_ ∗ _)%I). iSplitL "A"; iAssumption. }
      iIntros "[A B]". iDestruct (wrap_wrap2 with "A") as "A". iDestruct (wrap_wrap2 with "B") as "B". iFrame.
  Qed.

  Definition modality_wrap s := Modality _ (modality_wrap_mixin s).
  Definition modality_wrap2 s := Modality _ (modality_wrap2_mixin s).

  Definition Refines2 (P: mProp): mProp := (∀ s, 𝑀_{s} (|==> (𝑊_{s} P)))%I.

  Theorem Refines2_spec: ∀ P Q, (P ⊢ Refines2 Q) <-> (∀ s, Wrap s P ⊢ Refines (Wrap s Q)).
  Proof.
    unfold Refines2. i. split; i.
    - iIntros "H".
      assert(T: ∀ s, P -∗ Wrap2 s (Refines (Wrap s Q))).
      { i. iIntros "A". iDestruct (H with "A") as "A". eauto. }
      clear H.
      iDestruct (@wrap2_adj0) as "T".
      { eauto. }
      iApply "T". eauto.
    - iIntros "A". iIntros (s). iApply wrap2_adj1; eauto.
  Qed.

  Lemma ref2_mono: forall P Q, Entails P Q -> Entails (Refines2 P) (Refines2 Q).
  Proof.
    unfold Refines2. ii; ss.
    iIntros "H". iIntros (s). iApply wrap2_mono; [|et].
    iIntros. iApply ref_mono; [|et]. eapply wrap_mono; et.
  Qed.

  Lemma ref2_intro: forall P, Entails P (Refines2 P).
  Proof.
    unfold Refines2.
    ii; ss.
    iIntros "H". iIntros (s).
    iApply wrap2_adj1; [|iAssumption].
    iIntros "H". iApply ref_intro. ss.
  Qed.

  Lemma ref2_elim: forall P, Entails (Refines2 (Refines2 P)) (Refines2 P).
  Proof.
    unfold Refines2.
    ii; ss. iIntros "H". iIntros (s).
    {
      iSpecialize ("H" $! s).
      iApply wrap2_mono; [|iAssumption].
      iIntros "H". iMod "H". iApply wrap2_adj0; [|et].
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
      iApply wrap2_adj1.
      2: { instantiate (1:= (_ ∗ _)%I). iSplitL "A"; iAssumption. }
      iIntros "[A B]".
      iDestruct (wrap_wrap2 with "A") as "A".
      iMod "A". iModIntro. iSplitL "A"; et.
    }
  Qed.

  Lemma wrap_ref2_commute: forall `{!WA.Idem} s P, 𝑊_{s} (Refines2 P) ⊢ Refines2 (𝑊_{s} P).
  Proof.
    i. unfold Refines2. iIntros "H". iIntros (s').
    - iApply wrap2_adj1; [|iAssumption]. iIntros "H".
      iDestruct (wrap_idem with "H") as "H".
      iDestruct (wrap_mono with "H") as "H".
      { iIntros "H". iSpecialize ("H" $! (s ⊕ s')). iAssumption. }
      iDestruct (wrap_wrap2 with "H") as "H".
      iMod "H". iModIntro. iApply wrap_idem. ss.
(*
W M |=> W P
--------------
M |=> W M P
*)
  Qed.

  Corollary Refines_Refines2_sub: ∀ P, (Refines2 P ⊢ |==> P)%I.
  Proof.
    unfold Refines2. i. iIntros "H". iSpecialize ("H" $! ε).
    iApply wrap2_unit. iApply wrap2_mono; [|et]. iIntros "H".
    iMod "H". iModIntro.
    iApply wrap_unit. ss.
  Qed.

  Definition CondRefines s (P Q: mProp): mProp := (∀ b, 𝑊_{b} P ==∗ (𝑊_{s ⊕ b} Q))%I.
  Theorem CondRefines_tcomp: ∀ s P0 Q0 P1 Q1, CondRefines s P0 Q0 -∗ CondRefines s P1 Q1 -∗ CondRefines s (P0 ∗ P1) (Q0 ∗ Q1).
  Proof.
    i. unfold CondRefines.
    iIntros "A B" (b) "C".
    iDestruct (wrap_sep with "C") as "[C D]".
    iSpecialize ("A" with "C"). iMod "A".
    iSpecialize ("B" with "D"). iMod "B".
    iModIntro. iApply wrap_sep; iFrame.
  Qed.

  Lemma wrap_equiv: forall s0 s1 P, s0 ≡ s1 -> (𝑊_{s0} P ⊢ 𝑊_{s1} P).
  Proof.
    ii. econs; ii; ss. des. esplits; et. rewrite <- H. ss.
  Qed.

  Theorem CondRefines_vcomp: ∀ s0 s1 P Q R, CondRefines s0 P Q -∗ CondRefines s1 Q R -∗ CondRefines (s0 ⊕ s1) P R.
  Proof.
    i. unfold CondRefines.
    iIntros "A B" (b) "C".
    iSpecialize ("A" with "C"). iMod "A".
    iSpecialize ("B" with "A"). iMod "B".
    iModIntro. iApply wrap_equiv.
    2: { iApply wrap_mono; et. }
    rewrite oplus_comm. rewrite <- ! oplus_assoc. f_equiv. rewrite oplus_comm. refl.
  Qed.

  Definition LCondRefines s (S0 T0 S1: mProp): mProp := (T0 -∗ CondRefines s S0 S1)%I.
  Lemma LCondRefines_vs: ∀ s S0 T0 S1, (LCondRefines s S0 T0 S1 ⊣⊢ (∀ b, (Wrap b S0 ∗ T0) ==∗ (Wrap (s ⊕ b) S1))).
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
      LCondRefines s0 S0 T0 S1 -∗ LCondRefines s1 S1 T1 S2 -∗ LCondRefines (s0 ⊕ s1) S0 (T0 ∗ T1) S2.
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
    iApply wrap_equiv; [|iAssumption].
    r_solve.
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



Notation "#=> P" := (bupd P) (at level 50).

Section IUPD.

  Context `{M: MRAS.t}.

  Definition IUpd (I: mProp): mProp -> mProp :=
    fun P => (I ==∗ (I ∗ P))%I.

  Lemma IUpd_intro I: forall P, P ⊢ IUpd I P.
  Proof.
    ii. iIntros "H INV". iModIntro. iFrame.
  Qed.

  Lemma IUpd_mono I: forall P Q, (P ⊢ Q) -> (IUpd I P ⊢ IUpd I Q).
  Proof.
    ii. unfold IUpd. iIntros "H INV".
    iPoseProof ("H" with "INV") as "> [H0 H1]". iModIntro.
    iFrame. iApply H. auto.
  Qed.

  Lemma IUpd_trans I: forall P, (IUpd I (IUpd I P)) ⊢ (IUpd I P).
  Proof.
    ii. unfold IUpd. iIntros "H INV".
    iPoseProof ("H" with "INV") as "> [H0 H1]".
    iApply "H1". auto.
  Qed.

  Lemma IUpd_frame_r I: forall P R, ((IUpd I P) ∗ R) ⊢ (IUpd I (P ∗ R)).
  Proof.
    ii. unfold IUpd. iIntros "[H0 H1] INV".
    iPoseProof ("H0" with "INV") as "> [H0 H2]".
    iModIntro. iFrame.
  Qed.

  Lemma Upd_IUpd I: forall P, bupd P ⊢ (IUpd I P).
  Proof.
    ii. unfold IUpd. iIntros "H INV". iFrame.
  Qed.

  Lemma mProp_bupd_mixin_IUpd I: BiBUpdMixin mPropp (IUpd I).
  Proof.
    econs.
    - ii. unfold bupd. unfold IUpd. rewrite H. auto.
    - apply IUpd_intro.
    - apply IUpd_mono.
    - apply IUpd_trans.
    - apply IUpd_frame_r.
  Qed.
  Global Instance mProp_bi_bupd_IUpd I: BiBUpd mPropp := {| bi_bupd_mixin := mProp_bupd_mixin_IUpd I |}.

  Notation "#=( Q )=> P" := ((@bupd (bi_car (@mPropp _)) (@bi_bupd_bupd (@mPropp _) (@mProp_bi_bupd_IUpd Q))) P) (at level 99).
  Notation "P =( I ) =∗ Q" := (P ⊢ #=( I )=> Q) (only parsing, at level 99) : stdpp_scope.
  Notation "P =( I )=∗ Q" := (P -∗ #=( I )=> Q)%I (at level 99): bi_scope.

  Lemma IUpd_unfold I P
    :
    #=(I)=> P ⊢ (I -∗ #=> (I ∗ P)).
  Proof.
    reflexivity.
  Qed.

  Lemma IUpd_sub_mon_alt P Q R
    :
    (∃ S, (Q ==∗ (P ∗ S)) ∗ ((P ∗ S) ==∗ Q))
      -∗
      (#=(P)=> R)
      -∗
      (#=(Q)=> R).
  Proof.
    iIntros "H0 H1 H2".
    iDestruct "H0" as (S) "[A B]".
    iPoseProof (IUpd_unfold with "H1") as "H1".
    iSpecialize ("A" with "H2"). iMod "A".
    iDestruct "A" as "[A C]".
    iSpecialize ("H1" with "A"). iMod "H1".
    iDestruct "H1" as "[A D]".
    iFrame. iApply "B". iFrame.
  Qed.
  (* Definition SubIProp (P Q: mProp): mProp := ⌜∃ R: mProp, Q ⊣⊢ P ∗ R⌝%I. This also satisfies all laws *)
  Definition SubIProp P Q: mProp :=
    (Q -∗ #=> (P ∗ (P -∗ #=> Q)))%I.

  Lemma SubIProp_refl P
    :
    ⊢ SubIProp P P.
  Proof.
    iIntros "H". iFrame. auto.
  Qed.

  Lemma SubIProp_trans P Q R
    :
    (SubIProp P Q)
      -∗
      (SubIProp Q R)
      -∗
      (SubIProp P R).
  Proof.
    iIntros "H0 H1 H2".
    iPoseProof ("H1" with "H2") as "> [H1 H2]".
    iPoseProof ("H0" with "H1") as "> [H0 H1]".
    iFrame. iModIntro. iIntros "H".
    iPoseProof ("H1" with "H") as "> H".
    iPoseProof ("H2" with "H") as "H". auto.
  Qed.

  Lemma SubIProp_sep_l P Q
    :
    ⊢ (SubIProp P (P ∗ Q)).
  Proof.
    iIntros "[H0 H1]". iFrame. auto.
  Qed.

  Lemma SubIProp_sep_r P Q
    :
    ⊢ (SubIProp Q (P ∗ Q)).
  Proof.
    iIntros "[H0 H1]". iFrame. auto.
  Qed.

  Lemma IUpd_sub_mon P Q R
    :
    (SubIProp P Q)
      -∗
      (#=(P)=> R)
      -∗
      (#=(Q)=> R).
  Proof.
    iIntros "H0 H1 H2".
    iPoseProof (IUpd_unfold with "H1") as "H1".
    iPoseProof ("H0" with "H2") as "> [H0 H2]".
    iPoseProof ("H1" with "H0") as "> [H0 H1]".
    iPoseProof ("H2" with "H0") as "H0". iFrame. auto.
  Qed.
End IUPD.
Notation "#=( Q )=> P" := ((@bupd (bi_car (@mProp _)) (@bi_bupd_bupd (@mProp _) (@mProp_bi_bupd_IUpd _ Q))) P) (at level 99).
Notation "P =( I ) =∗ Q" := (P ⊢ #=( I )=> Q) (only parsing, at level 99) : stdpp_scope.
Notation "P =( I )=∗ Q" := (P -∗ #=( I )=> Q)%I (at level 99): bi_scope.



Section CAL.
  Local Set Default Proof Using "Type*".

  Context `{MRAS.t}.

  Definition layering (L M R: mProp): mProp := (L ∗ M -∗ |==> R)%I.
  Notation "L ⊨ M ; R" := (layering L M R) (at level 50).

  Notation "P ==* Q" := (bi_wand P (#=> Q)) (at level 50).
  Theorem layer_weaken: ∀ L M R L' M' R', ⊢ (L ==* L' -∗ M ==* M' -∗ R' ==* R -∗ L' ⊨ M' ; R' -∗ L ⊨ M ; R).
  Proof.
    i. iIntros "A B C T [D E]".
    iSpecialize ("A" with "D").
    iSpecialize ("B" with "E").
    iMod "A". iMod "B".
    iSpecialize ("T" with "[A B]").
    { iFrame. }
    iMod "T". iApply "C". ss.
  Qed.

  Theorem layer_minus: ∀ L M R L' M' R', ⊢ ((L' ⊨ M' ; R') -∗ (L ∗ M ==∗ L' ∗ M') -∗ (R' ==* R) -∗ L ⊨ M ; R).
  Proof.
    i. iIntros "A B C [D E]".
    iSpecialize ("B" with "[D E]"); iFrame.
    iMod "B".
    iSpecialize ("A" with "B").
    iMod "A".
    iApply "C"; eauto.
  Qed.

  Theorem layer_minus': ∀ L M R L' M' R', ((L' ⊨ M' ; R') -∗ ((L ==∗ L') -∗ (M ==∗ M') -∗ (R' ==* R) -∗ L ⊨ M ; R)).
  Proof.
    i.
    iIntros "A B C D".
    (* iIntros "A [B [C D]]". *)
    iApply (layer_minus with "[A] [B C] [D]"); iFrame.
    iIntros "[P Q]". iSpecialize ("B" with "P"). iSpecialize ("C" with "Q"). iMod "B". iMod "C".
    iModIntro. iFrame.
  Qed.


  Remark lle_ub_left: ∀ L M, ⊢ (L ⊨ M ; L).
  Proof.
    i. iIntros "[A B]". iModIntro. iFrame.
  Qed.

  Theorem empty: ∀ L, ⊢ L ⊨ emp%I ; L.
  Proof.
    i. iIntros "[A B]". iModIntro. iFrame.
  Qed.

  Theorem vcomp: ∀ (L1 M L2 N L3: mProp), (L1 ⊨ M ; L2) -∗ (L2 ⊨ N ; L3) -∗ (L1 ⊨ M ∗ N ; L3).
  Proof.
    i. unfold layering. iIntros "A B". iIntros "[C [D E]]".
    iSpecialize ("A" with "[C D]"); [iFrame|].
    iMod "A". iApply "B". iFrame.
  Qed.

  Theorem tcomp: ∀ (L1 L2 L1' M L2' N: mProp), (L1 ⊨ M ; L1') -∗ (L2 ⊨ N ; L2') -∗ ((L1 ∗ L2) ⊨ M ∗ N ; (L1' ∗ L2')).
  Proof.
    i. unfold layering. iIntros "A B [[C D] [E F]]".
    iSpecialize ("A" with "[C E]"); [iFrame|].
    iSpecialize ("B" with "[D F]"); [iFrame|].
    iMod "A". iMod "B". iFrame. eauto.
  Qed.

  Theorem layer_transfer: ∀ L M R R', ((R' ∗ L) ⊨ M ; R ⊣⊢ L ⊨ M ; (R' ==∗ R)).
  Proof.
    i. iSplit.
    - iIntros "A [B D]". iModIntro. iIntros "C". iSpecialize ("A" with "[C B D]"); iFrame.
    - iIntros "A [[B C] D]". iSpecialize ("A" with "[C D]"); iFrame. iMod "A". iApply "A". ss.
  Qed.

  Goal ∀ L0 L1 L2 L3 C0 C1 C2, (L0 ⊨ C0 ; (L0 ∗ L1)) -∗ (L1 ⊨ C1 ; L2) -∗ (L0 ⊨ C2 ; L3) -∗ (L0 ⊨ (C0 ∗ C1 ∗ C2) ; (L2 ∗ L3)).
  Proof.
    i.
    iIntros "A B C".
    iApply layer_weaken.
    { instantiate (1:=(L0 ∗ emp)%I). eauto. }
    { instantiate (1:=(C0 ∗ (C1 ∗ C2))%I). eauto. }
    { instantiate (1:=((L0 ∗ L1) ∗ ((L0 ∗ L1) ==∗ (L2 ∗ L3)))%I). iIntros "[A B]". iSpecialize ("B" with "A"). eauto. }
    iApply (tcomp with "A").
    iApply layer_transfer.
    iApply layer_weaken.
    { instantiate (1:=(L1 ∗ L0)%I). iIntros "[[A B] C]". iModIntro. iFrame. }
    { instantiate (1:=(C1 ∗ C2)%I). eauto. }
    { instantiate (1:=(L2 ∗ L3)%I). eauto. }
    iApply (tcomp with "B"); eauto.
  Qed.

End CAL.
