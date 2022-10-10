Require Import sflib.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.PropExtensionality.
Require Import IProp PCM IPM IProofMode2.
Require Import Program Coqlib.

Set Implicit Arguments.

Section SEALED_UPD.
  Context `{Σ: GRA.t}.

  Definition sealed_upd (X P: iProp) :=
    (∀ A, X ∧ A ==∗ (X ∧ A ** P))%I.

  Lemma sealed_upd_ret X P
    :
    P -∗ sealed_upd X P.
  Proof.
    unfold sealed_upd.
    iIntros "H0 % H1". iFrame.
    iModIntro. ss.
  Qed.

  Lemma sealed_upd_special0
        (x p q: Σ)
        (UPD: URA.updatable (x ⋅ p) (x ⋅ q))
    :
    sealed_upd (Own x) (Own p) -∗ sealed_upd (Own x) (Own q)
  .
  Proof.
    unfold sealed_upd. iIntros. iDes.
    iSpecialize ("A0" with "A"). iMod "A0".
    iStopProof.
    uipropall. i. des. subst.
    rr in H0. rr in H1. des. subst.
    esplits; try apply H2; try assumption.
    2: { rr. exists ctx0. r_solve. }
    3: { i. instantiate (1:= x ⋅ q ⋅ ctx0 ⋅ ctx).
         replace (x ⋅ q ⋅ ctx0 ⋅ ctx ⋅ ctx1) with (x ⋅ q ⋅ (ctx0 ⋅ ctx ⋅ ctx1)) by r_solve.
         eapply UPD. r_wf H.
    }
    { instantiate (1:=q ⋅ ctx). r_solve. }
    { rr. exists ctx. r_solve. }
  Qed.

  Lemma sealed_upd_special1
        (x p: Σ)
        (VALID: URA.wf x)
    :
    sealed_upd (Own x) (Own p) -∗ ⌜URA.wf (x ⋅ p)⌝
  .
  Proof.
    (*** this is not needed. already included in the definition of isim ***)
  Abort.

  Lemma sealed_upd_bind X P Q
    :
    (P -∗ sealed_upd X Q) -∗ sealed_upd X P -∗ sealed_upd X Q.
  Proof.
    unfold sealed_upd.
    iIntros "H0 H1 % H2".
    iPoseProof ("H1" $! A with "H2") as "H1".
    iMod "H1".
    iDes.
    iPoseProof ("H0" with "A") as "H0".
    iApply ("H0" $! A with "H1").
  Qed.

  Lemma sealed_upd_join X P
    :
    sealed_upd X (sealed_upd X P) -∗ sealed_upd X P.
  Proof.
    unfold sealed_upd.
    iIntros "H0 % H1".
    iPoseProof ("H0" $! _ with "H1") as "H0".
    iMod "H0". iDes.
    iApply ("A" $! _ with "H0").
  Qed.

  Lemma sealed_upd_mon X Y P
    :
    (Y -∗ X) -∗ sealed_upd X P -∗ sealed_upd Y P.
  Proof.
    unfold sealed_upd.
    iIntros "H0 H1 % H2".
    iSpecialize ("H1" $! (Y ∧ A))%I.
    iAssert (X ∧ Y ∧ A)%I with "[H0 H2]" as "H0".
    { iSplit; auto. iDestruct "H2" as "[H2 _]". iApply ("H0" with "H2"). }
    iSpecialize ("H1" with "H0"). iMod "H1". iModIntro. iDes. iFrame. iDestruct "H1" as "[_ B]". eauto.
  Qed.

  Lemma sealed_upd_map X P Q
    :
    (P -∗ Q) -∗ sealed_upd X P -∗ sealed_upd X Q.
  Proof.
    unfold sealed_upd.
    iIntros "H0 H1 % H2".
    iSpecialize ("H1" with "H2"). iMod "H1". iDes. iModIntro. iFrame. iApply "H0"; eauto.
  Qed.

  Lemma sealed_upd_emp X
    :
    ⊢ sealed_upd X emp%I.
  Proof.
    unfold sealed_upd.
    iIntros "% H0". iFrame.
    iModIntro. eauto.
  Qed.

  Lemma sealed_upd_top P
    :
    sealed_upd True P ==∗ P.
  Proof.
    unfold sealed_upd.
    iIntros "H0". iPoseProof ("H0" $! True)%I as "H0".
    iAssert (True ∧ True)%I as "H1".
    { auto. }
    iPoseProof ("H0" with "H1") as "[_ H0]". iFrame.
  Qed.

  Lemma sealed_upd_upd X P
    :
    ((|==> P) -∗ sealed_upd X P)
  .
  Proof.
    unfold sealed_upd.
    iIntros. iDes. iMod "A0". iModIntro. iFrame.
  Qed.

  Lemma sealed_upd_sep X P Q
    :
    (sealed_upd X P) -∗ (sealed_upd X Q) -∗ sealed_upd X (P ** Q).
  Proof.
    unfold sealed_upd.
    iIntros "H0 H1 % H2".
    iPoseProof ("H0" $! A with "H2") as "H0". iMod "H0". iDes.
    iPoseProof ("H1" $! A with "H0") as "H1". iMod "H1". iDes.
    iModIntro. iFrame.
  Qed.

  Lemma sealed_upd_unseal X P
    :
    X -∗ (sealed_upd X P) -∗ |==> (X ** P).
  Proof.
    unfold sealed_upd.
    iIntros "H0 H1".
    iAssert (X ∧ True)%I with "[H0]" as "H0".
    { auto. }
    iPoseProof ("H1" $! _ with "H0") as "H1". iMod "H1". iModIntro. iDes. iFrame.
  Qed.

  Lemma sealed_upd_sep_accum X P Q
    :
    P -∗ (sealed_upd (X ** P) Q) -∗ sealed_upd X (P ** Q).
  Proof.
    unfold sealed_upd.
    iIntros "H0 H1" (A) "H2".
    iAssert ((X ** P) ∧ (X ∧ A ** P))%I with "[H0 H2]" as "H0".
    { iSplit; iFrame. iDestruct "H2" as "[H2 _]". auto. }
    iPoseProof ("H1" $! _ with "H0") as "H1". iMod "H1". iModIntro. iDes. iFrame.
    iDestruct "H1" as "[_ $]".
  Qed.

  Corollary sealed_upd_viewshift X P Q
    :
    (P ==∗ Q) -∗ (sealed_upd X P) -∗ (sealed_upd X Q).
  Proof.
    iIntros. iDes.
    iApply sealed_upd_join.
    iApply (sealed_upd_map with "[A0]"); [|eauto].
    iIntros. iDes. iSpecialize ("A0" with "A").
    iApply sealed_upd_upd. ss.
  Qed.

  Corollary sealed_upd_elim_upd X P
    :
    (sealed_upd X (|==> P)) -∗ (sealed_upd X P).
  Proof.
    iIntros. iDes.
    iApply sealed_upd_viewshift; [|eauto].
    eauto.
  Qed.

  Corollary sealed_upd_intro_upd X P
    :
    (sealed_upd X P) -∗ (sealed_upd X (|==> P)).
  Proof.
    iIntros. iDes.
    iApply sealed_upd_map; [|eauto].
    iIntros. iModIntro. iFrame.
  Qed.

  Example sealed_upd_map_pure X P Q
        (H: P ⊢ Q)
    :
     sealed_upd X P ⊢ sealed_upd X Q.
  Proof.
    iIntros. iDes.
    iApply sealed_upd_map; [|eauto].
    iIntros. iStopProof. ss.
  Qed.

  Example sealed_upd_viewshift_pure X P Q
            (H: P ==∗ Q)
    :
    (sealed_upd X P) -∗ (sealed_upd X Q).
  Proof.
    iIntros. iDes.
    iApply sealed_upd_viewshift; [|eauto].
    iIntros. iStopProof. eauto.
  Qed.

  Corollary sealed_upd_equiv_upd P
    :
    sealed_upd emp P ⊣⊢ (|==> P)
  .
  Proof.
    iSplit; iIntros; iDes.
    - iDestruct (sealed_upd_unseal with "[] [A]") as "H".
      { instantiate (1:=emp%I). eauto. }
      { eauto. }
      iMod "H". iModIntro. iDes. iFrame.
    - iApply sealed_upd_upd; eauto.
  Qed.

End SEALED_UPD.


Section UNFOLD.
  Context `{Σ: GRA.t}.

  Lemma sealed_upd_unfold P (rx r: Σ)
    (WF: URA.wf (r ⋅ rx)) (UPD: (sealed_upd (Own rx) P) r)
    :
    ∃ rp, URA.updatable (rx ⋅ r) (rx ⋅ rp) /\ P rp
  .
  Proof.
    unfold sealed_upd in *.
    eapply from_semantic in UPD.
    (* eassert(Own r ⊢ #=> (Own X ∧ P ==∗ Own X ∧ P ** P)). *)
    eassert(Own (r ⋅ rx) ⊢ #=> _).
    { iIntros "[H B]". iDestruct (UPD with "H") as "H". iMod "H".
      iSpecialize ("H" $! (Own rx)).
      (* iSpecialize ("H" $! P). *)
      iSpecialize ("H" with "[B]").
      { eauto. }
      iMod "H".
      iModIntro.
      iDestruct "H" as "[[H _] B]".
      iCombine "H B" as "H".
      iAssumption. }
    clear UPD.
    eapply to_semantic in H; eauto.
    uipropall. des. subst.
    esplits; eauto.
    etrans; et. { rewrite URA.add_comm. et. }
    eapply URA.updatable_add; try refl.
    eapply URA.extends_updatable; et.
  Qed.

  (* Program Definition SealedUpd (X P: iProp): iProp' := *)
  (*   Seal.sealing *)
  (*     "iProp" *)
  (*     (iProp_intro (fun r0 => forall rx (WF: URA.wf (r0 ⋅ rx)), *)
  (*                       X rx -> exists r1, P r1 /\ *)
  (*            (forall ctx, URA.wf (rx ⋅ r0 ⋅ ctx) -> URA.wf (rx ⋅ r1 ⋅ ctx))) _). *)
  (* Next Obligation. *)
  (*   exploit H; eauto. { admit "". } i; des. *)
  (*   esplits; eauto. i. *)
  (*   eapply x1. *)
  (*   eapply URA.wf_extends; et. *)
  (*   eapply URA.extends_add. *)
  (*   erewrite (URA.add_comm _ r0). *)
  (*   erewrite (URA.add_comm _ r1). *)
  (*   eapply URA.extends_add. ss. *)
  (* Qed. *)

  (* (* Lemma iProp_eta x0 x1 y0 y1 (EQ: x0 = x1) *) *)
  (* (*   : *) *)
  (* (*   iProp_intro x0 y0 = iProp_intro x1 y1 *) *)
  (* (* . *) *)
  (* (* Proof. *) *)
  (* (*   subst. f_equal. eapply proof_irr. *) *)
  (* (* Qed. *) *)

  (* Theorem sealed_upd_unfold X P *)
  (*   : *)
  (*   sealed_upd X P = SealedUpd X P *)
  (* . *)
  (* Proof. *)
  (*   Fail extensionality r. *)
  (*   Fail eapply Axioms.prop_ext. *)
  (*   Fail eapply iProp_eta. *)
  (* Abort. *)
  (* (*** there really is no way to do this? ***) *)

  (* Theorem sealed_upd_unfold r X P *)
  (*   : *)
  (*   sealed_upd X P r = SealedUpd X P r *)
  (* . *)
  (* Proof. *)
  (*   unfold sealed_upd, SealedUpd. *)
  (*   eapply Axioms.prop_ext. split; i. *)
  (*   - rr. rewrite Seal.sealing_eq. *)
  (*     i. *)
  (*     rr in H. rewrite Seal.sealing_eq in H. *)
  (*     specialize (H P). *)
  (*     rr in H. rewrite Seal.sealing_eq in H. *)
  (*     specialize (H rx). spc H. *)
  (*     rr in H. rewrite Seal.sealing_eq in H. *)
  (*     exploit H. *)
  (*     { uipropall. des. *)
  (* Qed. *)

End UNFOLD.
