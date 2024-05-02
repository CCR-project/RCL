Require Import Algebra Coqlib.
Require Import String RCLIPM.
Set Implicit Arguments.
Open Scope string_scope.
Open Scope list_scope.



Section TUTORIAL.

Context `{M: MRAS.t}.
(*** Section 3.1 ***)
Goal ∀ (a0 a1 b0 b1 c0 c1: mProp),
    (a0 ==∗ a1) -> ((a1 ∗ b0) ==∗ (a1 ∗ b1)) -> ((a1 ∗ c0) ==∗ (a1 ∗ c1))
    -> ((a0 ∗ b0 ∗ c0) ==∗ (a1 ∗ b1 ∗ c1))
.
Proof.
  i.
  {
    iIntros "[? [? ?]]".
    iDestruct (H with "[$]") as ">?". iDestruct (H0 with "[$]") as ">[? $]".
    iDestruct (H1 with "[$]") as "$".
  }
Qed.


Goal forall a0 a1 b0 b1 c0 c1,
    a0 ⊑ a1 -> a1 ⊕ b0 ⊑ a1 ⊕ b1 -> a1 ⊕ c0 ⊑ a1 ⊕ c1 ->
    a0 ⊕ b0 ⊕ c0 ⊑ a1 ⊕ b1 ⊕ c1.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  erewrite oplus_comm_weak with (b:=c0).
  erewrite <- oplus_comm_weak with (a:=c1).
  rewrite ! oplus_assoc_weak2.
  apply ref_oplus; [|reflexivity].
  erewrite oplus_comm_weak with (b:=a1).
  erewrite <- oplus_comm_weak with (b:=c1).
  rewrite H1.
  reflexivity.
Qed.

(*** Section 3.1, but with one more module. ***)
Goal ∀ (a0 a1 b0 b1 c0 c1 d0 d1: mProp),
    (a0 ==∗ a1) -> ((a1 ∗ b0) ==∗ (a1 ∗ b1)) -> ((a1 ∗ c0) ==∗ (a1 ∗ c1)) -> ((a1 ∗ d0) ==∗ (a1 ∗ d1))
    -> ((a0 ∗ b0 ∗ c0 ∗ d0) ==∗ (a1 ∗ b1 ∗ c1 ∗ d1))
.
Proof.
  i.
  {
    iIntros "[? [? [? ?]]]".
    iDestruct (H with "[$]") as ">?". iDestruct (H0 with "[$]") as ">[? $]".
    iDestruct (H1 with "[$]") as ">[? $]". iDestruct (H2 with "[$]") as "$".
  }
Qed.

Goal forall a0 a1 b0 b1 c0 c1 d0 d1,
    a0 ⊑ a1 -> a1 ⊕ b0 ⊑ a1 ⊕ b1 -> a1 ⊕ c0 ⊑ a1 ⊕ c1 -> a1 ⊕ d0 ⊑ a1 ⊕ d1 ->
    a0 ⊕ b0 ⊕ c0 ⊕ d0 ⊑ a1 ⊕ b1 ⊕ c1 ⊕ d1.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  erewrite oplus_comm_weak with (b:=c0).
  (*new*)  erewrite oplus_comm_weak with (b:=d0).
  erewrite <- oplus_comm_weak with (a:=c1).
  (*new*)  erewrite <- oplus_comm_weak with (a:=d1).
  rewrite ! oplus_assoc_weak2.
  apply ref_oplus; [|reflexivity].
  erewrite oplus_comm_weak with (b:=a1).
  erewrite <- oplus_comm_weak with (a:=a1).
  (*new*)  rewrite ! oplus_assoc_weak2.
  (*new*)  rewrite H2.
  (*new*)  erewrite oplus_comm_weak with (b:=c0).
  (*new*)  erewrite <- oplus_comm_weak with (a:=c1).
  (*new*)  rewrite ! oplus_assoc_weak2.
  (*new*)  apply ref_oplus; [|reflexivity].
  (*new*)  erewrite oplus_comm_weak with (b:=a1).
  (*new*)  erewrite <- oplus_comm_weak with (a:=a1).
  rewrite H1.
  reflexivity.
Qed.

(*** Section 3.1, but with two more modules. ***)
Goal ∀ (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1: mProp),
    (a0 ==∗ a1) -> ((a1 ∗ b0) ==∗ (a1 ∗ b1)) -> ((a1 ∗ c0) ==∗ (a1 ∗ c1)) -> ((a1 ∗ d0) ==∗ (a1 ∗ d1)) -> ((a1 ∗ e0) ==∗ (a1 ∗ e1))
    -> ((a0 ∗ b0 ∗ c0 ∗ d0 ∗ e0) ==∗ (a1 ∗ b1 ∗ c1 ∗ d1 ∗ e1))
.
Proof.
  i.
  {
    iIntros "[? [? [? [? ?]]]]".
    iDestruct (H with "[$]") as ">?". iDestruct (H0 with "[$]") as ">[? $]".
    iDestruct (H1 with "[$]") as ">[? $]". iDestruct (H2 with "[$]") as ">[? $]".
    iDestruct (H3 with "[$]") as "$".
  }
Qed.

Goal forall a0 a1 b0 b1 c0 c1 d0 d1 e0 e1,
    a0 ⊑ a1 -> a1 ⊕ b0 ⊑ a1 ⊕ b1 -> a1 ⊕ c0 ⊑ a1 ⊕ c1 -> a1 ⊕ d0 ⊑ a1 ⊕ d1 -> a1 ⊕ e0 ⊑ a1 ⊕ e1 ->
    a0 ⊕ b0 ⊕ c0 ⊕ d0 ⊕ e0 ⊑ a1 ⊕ b1 ⊕ c1 ⊕ d1 ⊕ e1.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  erewrite oplus_comm_weak with (b:=c0).
  erewrite oplus_comm_weak with (b:=d0).
  (*new*)  erewrite oplus_comm_weak with (b:=e0).
  erewrite <- oplus_comm_weak with (a:=c1).
  erewrite <- oplus_comm_weak with (a:=d1).
  (*new*) erewrite <- oplus_comm_weak with (a:=e1).
  rewrite ! oplus_assoc_weak2.
  apply ref_oplus; [|reflexivity].
  erewrite oplus_comm_weak with (b:=a1).
  erewrite <- oplus_comm_weak with (a:=a1).
  rewrite ! oplus_assoc_weak2.
  rewrite H3.
  erewrite oplus_comm_weak with (b:=c0).
  (*new*)  erewrite oplus_comm_weak with (b:=d0).
  erewrite <- oplus_comm_weak with (a:=c1).
  (*new*)  erewrite <- oplus_comm_weak with (a:=d1).
  rewrite ! oplus_assoc_weak2.
  apply ref_oplus; [|reflexivity].
  erewrite oplus_comm_weak with (b:=a1).
  erewrite <- oplus_comm_weak with (a:=a1).
  (*new*)  rewrite ! oplus_assoc_weak2.
  (*new*)  rewrite H1.
  (*new*)  erewrite oplus_comm_weak with (b:=d0).
  (*new*)  erewrite <- oplus_comm_weak with (a:=d1).
  (*new*)  rewrite ! oplus_assoc_weak2.
  (*new*)  apply ref_oplus; [|reflexivity].
  (*new*)  erewrite oplus_comm_weak with (b:=a1).
  (*new*)  erewrite <- oplus_comm_weak with (a:=a1).
  rewrite H2.
  reflexivity.
Qed.

(*** Here, m is the memory module ***)
Section CCRFOS.
Variable m0 m1 m2 s0 s1 s2 s3 s4 s5 s6 e0 e1 e2 e3 e4: M.
Hypothesis MEMOPENPROOF: m0 ⊑ m1.
Hypothesis STACKIMP0PROOF: s0 ⊑ s1.
Hypothesis STACK01PROOF: s1 ⊑ s2.
Hypothesis ADEQUACYOPEN: m1 ⊕ s2 ⊑ m2 ⊕ s3.
Hypothesis MEMOPEN0PROOF: m2 ⊑ m0.
Hypothesis STACK12PROOF: s3 ⊑ s4.
Hypothesis STACK23PROOF: s4 ⊑ s5.
Hypothesis ECHOIMP0PROOF: e0 ⊑ e1.
Hypothesis ECHO01PROOF: e1 ⊑ e2.
Hypothesis ADEQUACYOPEN2: s5 ⊕ e2 ⊑ s6 ⊕ e3.
Hypothesis STACK32PROOF: s6 ⊑ s4.
Hypothesis ECHOMONPROOF: e3 ⊑ e4.
(** 17 aux tactics, 12 main tactics **)
Example CCR: m0 ⊕ s0 ⊕ e0 ⊑ m0 ⊕ s4 ⊕ e4.
  transitivity (m1 ⊕ s2 ⊕ e0).
  {
    rewrite <- ! oplus_assoc.
    eapply ref_oplus.
    { eapply MEMOPENPROOF. }
    eapply ref_oplus; [|refl].
    { etrans.
      { eapply STACKIMP0PROOF. }
      { eapply STACK01PROOF. }
    }
  }
  etrans.
  { eapply ref_oplus; [|refl].
    eapply ADEQUACYOPEN.
  }
  rewrite <- ! oplus_assoc.
  eapply ref_oplus.
  { eapply MEMOPEN0PROOF. }
  transitivity (s5 ⊕ e2).
  {
    eapply ref_oplus.
    { etrans.
      { eapply STACK12PROOF. }
      { eapply STACK23PROOF. }
    }
    { etrans.
      { eapply ECHOIMP0PROOF. }
      { eapply ECHO01PROOF. }
    }
  }
  etrans.
  {
    eapply ADEQUACYOPEN2.
  }
  {
    eapply ref_oplus.
    { eapply STACK32PROOF. }
    { eapply ECHOMONPROOF. }
  }
Qed.



Variable sch0 sch1 c0 t0 mt1 cmt1: M.
Hypothesis SCHEDPROOF: ∀ c, sch0 ⊕ c ⊑ sch1 ⊕ c.
Hypothesis TICKETLOCKPROOF: m0 ⊕ t0 ⊑ m0 ⊕ mt1.
Hypothesis CLIENTPROOF: sch1 ⊕ (m0 ⊕ c0 ⊕ mt1) ⊑ sch1 ⊕ (m0 ⊕ cmt1).
Let right_mono: ∀ (x y0 y1: M), y0 ⊑ y1 -> x ⊕ y0 ⊑ x ⊕ y1. Proof. i. rewrite H. refl. Qed.
Let left_mono: ∀ (x y0 y1: M), y0 ⊑ y1 -> y0 ⊕ x ⊑ y1 ⊕ x. Proof. i. rewrite H. refl. Qed.
(* 23 aux tactics, 3 main tactics *)
Example FOS2: sch0 ⊕ m0 ⊕ c0 ⊕ t0 ⊑ sch1 ⊕ m0 ⊕ cmt1.
Proof.
  erewrite SCHEDPROOF.
  etrans.
  { rewrite <- ! oplus_assoc.
    eapply right_mono.
    rewrite oplus_assoc.
    rewrite oplus_comm.
    rewrite oplus_assoc.
    rewrite oplus_comm.
    eapply right_mono.
    rewrite oplus_comm.
    eapply TICKETLOCKPROOF.
  }
  assert(T: (c0 ⊕ (m0 ⊕ mt1)) ⊑ (m0 ⊕ c0 ⊕ mt1)).
  { rewrite oplus_assoc. rewrite oplus_comm. rewrite oplus_assoc. rewrite oplus_comm.
    rewrite <- oplus_assoc. eapply right_mono. rewrite oplus_comm. refl. }
  rewrite T.
  etrans.
  { eapply CLIENTPROOF. }
  rewrite oplus_assoc.
  refl.
Qed.
(* 33 aux tactics, 3 main tactics *)
Example TOGETHER: m0 ⊕ s0 ⊕ e0 ⊕ sch0 ⊕ c0 ⊕ t0 ⊑ m0 ⊕ s4 ⊕ e4 ⊕ sch1 ⊕ cmt1.
Proof.
  etrans.
  { eapply left_mono. eapply left_mono. eapply left_mono. eapply CCR. }
  etrans.
  { eapply left_mono.
    eapply left_mono.
    eapply left_mono.
    rewrite <- ! oplus_assoc.
    rewrite oplus_comm.
    refl.
  }
  etrans; cycle 1.
  { eapply left_mono.
    eapply left_mono.
    rewrite <- ! oplus_assoc.
    rewrite oplus_comm.
    refl.
  }
  rewrite <- ! oplus_assoc.
  eapply right_mono.
  eapply right_mono.
  rewrite ! oplus_assoc.
  etrans.
  { do 2 eapply left_mono. erewrite oplus_comm. refl. }
  rewrite FOS2.
  rewrite oplus_comm. rewrite oplus_assoc.
  rewrite oplus_comm. rewrite <- oplus_assoc.
  eapply right_mono.
  rewrite oplus_comm. refl.
Qed.
End CCRFOS.



Section CCRFOS_RCL.
Variable m0 m1 m2 s0 s1 s2 s3 s4 s5 s6 e0 e1 e2 e3 e4: M.
Hypothesis MEMOPENPROOF: Own m0 ==∗ Own m1.
Hypothesis STACKIMP0PROOF: Own s0 ==∗ Own s1.
Hypothesis STACK01PROOF: Own s1 ==∗ Own s2.
Hypothesis ADEQUACYOPEN: Own m1 ∗ Own s2 ==∗ (Own m2 ∗ Own s3).
Hypothesis MEMOPEN0PROOF: Own m2 ==∗ Own m0.
Hypothesis STACK12PROOF: Own s3 ==∗ Own s4.
Hypothesis STACK23PROOF: Own s4 ==∗ Own s5.
Hypothesis ECHOIMP0PROOF: Own e0 ==∗ Own e1.
Hypothesis ECHO01PROOF: Own e1 ==∗ Own e2.
Hypothesis ADEQUACYOPEN2: Own s5 ∗ Own e2 ==∗ (Own s6 ∗ Own e3).
Hypothesis STACK32PROOF: Own s6 ==∗ Own s4.
Hypothesis ECHOMONPROOF: Own e3 ==∗ Own e4.
Ltac iDone := iFrame; eauto.
(** 2 aux tactics, 12 main tactics **)
(* Example CCRRCL: (Own m0) ∗ Own s0 ∗ Own e0 ==∗ (Own m0 ∗ Own s4 ∗ Own e4). *)
Example CCRRCL: Own s0 ∗ Own e0 -∗ IUpd (Own m0) (Own s4 ∗ Own e4).
Proof.
  iIntros "[? ?] ?".
  iDestruct (MEMOPENPROOF with "[$]") as ">?".
  iDestruct (STACKIMP0PROOF with "[$]") as ">?".
  iDestruct (STACK01PROOF with "[$]") as ">?".
  iDestruct (ADEQUACYOPEN with "[$]") as ">[? ?]".
  iDestruct (MEMOPEN0PROOF with "[$]") as ">?".
  iDestruct (STACK12PROOF with "[$]") as ">?".
  iDestruct (STACK23PROOF with "[$]") as ">?".
  iDestruct (ECHOIMP0PROOF with "[$]") as ">?".
  iDestruct (ECHO01PROOF with "[$]") as ">?".
  iDestruct (ADEQUACYOPEN2 with "[$]") as ">[? ?]".
  iDestruct (STACK32PROOF with "[$]") as ">?".
  iDestruct (ECHOMONPROOF with "[$]") as ">?".
  iDone.
Qed.
Global Instance upd_elim_iupd I P Q
       `{ElimModal _ True false false (IUpd I P) P Q R}
  :
  ElimModal True false false (#=> P) P Q R.
Proof.
  unfold ElimModal. i. iIntros "[H0 H1]".
  iPoseProof (Upd_IUpd with "H0") as "> H0". iApply "H1". auto.
Qed.

Global Instance iupd_elim_upd I P Q b
  :
  ElimModal True b false (#=> P) P (IUpd I Q) (IUpd I Q).
Proof.
  unfold ElimModal. i. iIntros "[H0 H1]".
  iPoseProof (Upd_IUpd with "H0") as "H0".
  iIntros "H". iPoseProof ("H0" with "H") as "> [H0 H2]".
  destruct b; ss.
  { iPoseProof ("H2") as "# > H2". iPoseProof ("H1" with "H2") as "H".
    iApply ("H" with "H0").
  }
  { iPoseProof ("H2") as "> H2". iPoseProof ("H1" with "H2") as "H".
    iApply ("H" with "H0").
  }
Qed.
Lemma IUpd_wand: forall I P Q, (P -∗ Q) -∗ (IUpd I P -∗ IUpd I Q).
Proof.
  ii. iIntros "A B".
  iDestruct (IUpd_frame_r with "[A B]") as "H".
  { iFrame. iAccu. }
  iApply IUpd_mono.
  2: { eauto. }
  iIntros "[A B]". iApply "B"; eauto.
Qed.
Global Instance iupd_elim_iupd I P Q b
  :
  ElimModal True b false (IUpd I P) P (IUpd I Q) (IUpd I Q).
Proof.
  unfold ElimModal. i. iIntros "[H0 H1]".
  destruct b; ss.
  { iDestruct (IUpd_wand with "H1 H0") as "H". iApply IUpd_trans. ss. }
  { iDestruct (IUpd_wand with "H1 H0") as "H". iApply IUpd_trans. ss. }
Qed.

Variable sch0 sch1 c0 t0 mt1 cmt1: mProp.
Hypothesis SCHEDPROOF: sch0 ==∗ sch1.
Hypothesis TICKETLOCKPROOF: t0 -∗ IUpd (Own m0) mt1.
Hypothesis CLIENTPROOF: sch1 ∗ (c0 ∗ mt1) -∗ IUpd (Own m0) (sch1 ∗ cmt1).
(* 2 aux tactics, 3 main tactics *)
Example FOS2RCL: sch0 ∗ (c0 ∗ t0) -∗ IUpd (Own m0) (sch1 ∗ cmt1).
Proof.
  iIntros "[? [? ?]]".
  iDestruct (SCHEDPROOF with "[$]") as ">?".
  iDestruct (TICKETLOCKPROOF with "[$]") as ">?".
  iDestruct (CLIENTPROOF with "[$]") as ">?".
  iDone.
Qed.
(* 2 aux tactics, 2 main tactics *)
Example TOGETHERRCL: Own s0 ∗ Own e0 ∗ sch0 ∗ c0 ∗ t0 -∗ IUpd (Own m0) (Own s4 ∗ Own e4 ∗ sch1 ∗ cmt1).
Proof.
  iIntros "[? [? [? [? ?]]]]".
  iDestruct (FOS2RCL with "[$]") as ">[? ?]".
  iDestruct (CCRRCL with "[$]") as ">[? ?]".
  iDone.
Qed.
End CCRFOS_RCL.

End TUTORIAL.
