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

Set Implicit Arguments.







Section SIM.

Section TY.
(* Context `{R: Type}. *)
Inductive _simg
          (simg: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (f_src f_tgt: bool): (itree eventE R0) -> (itree eventE R1) -> Prop :=
| simg_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg simg RR f_src f_tgt (Ret r_src) (Ret r_tgt)
| simg_syscall
    ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR true true (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg RR f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)

| simg_tauL
    itr_src0 itr_tgt0
    (TAUL: True)
    (SIM: @_simg simg _ _ RR true f_tgt itr_src0 itr_tgt0)
  :
    _simg simg RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
| simg_tauR
    itr_src0 itr_tgt0
    (TAUR: True)
    (SIM: @_simg simg _ _ RR f_src true itr_src0 itr_tgt0)
  :
    _simg simg RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

| simg_chooseL
    X ktr_src0 itr_tgt0
    (CHOOSEL: True)
    (SIM: exists x, _simg simg RR true f_tgt (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
| simg_chooseR
    X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (SIM: forall x, _simg simg RR f_src true itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

| simg_takeL
    X ktr_src0 itr_tgt0
    (TAKEL: True)
    (SIM: forall x, _simg simg RR true f_tgt (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)
| simg_takeR
    X itr_src0 ktr_tgt0
    (TAKER: True)
    (SIM: exists x, _simg simg RR f_src true itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0)

| simg_progress
    itr_src itr_tgt
    (SIM: simg _ _ RR false false itr_src itr_tgt)
    (SRC: f_src = true)
    (TGT: f_tgt = true)
  :
    _simg simg RR f_src f_tgt itr_src itr_tgt
.

Lemma _simg_ind2 (r: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop)
      R0 R1 (RR: R0 -> R1 -> Prop)
      (P: bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop)
      (RET: forall
          f_src f_tgt
          r_src r_tgt
          (SIM: RR r_src r_tgt),
          P f_src f_tgt (Ret r_src) (Ret r_tgt))
      (SYSCALL: forall
          f_src f_tgt
          ktr_src0 ktr_tgt0 fn varg rvs
          (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), r _ _ RR true true (ktr_src0 x_src) (ktr_tgt0 x_tgt)),
          P f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0))
      (TAUL: forall
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUL: True)
          (SIM: _simg r RR true f_tgt itr_src0 itr_tgt0)
          (IH: P true f_tgt itr_src0 itr_tgt0),
          P f_src f_tgt (tau;; itr_src0) (itr_tgt0))
      (TAUR: forall
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUR: True)
          (SIM: _simg r RR f_src true itr_src0 itr_tgt0)
          (IH: P f_src true itr_src0 itr_tgt0),
          P f_src f_tgt (itr_src0) (tau;;itr_tgt0))
      (CHOOSEL: forall
          f_src f_tgt
          X ktr_src0 itr_tgt0
          (CHOOSEL: True)
          (SIM: exists x, <<SIM: _simg r RR true f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P true f_tgt (ktr_src0 x) itr_tgt0>>),
          P f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0))
      (CHOOSER: forall
          f_src f_tgt
          X itr_src0 ktr_tgt0
          (CHOOSER: True)
          (SIM: forall x, <<SIM: _simg r RR f_src true itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src true itr_src0 (ktr_tgt0 x)>>),
          P f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0))
      (TAKEL: forall
          f_src f_tgt
          X ktr_src0 itr_tgt0
          (TAKEL: True)
          (SIM: forall x, <<SIM: _simg r RR true f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P true f_tgt (ktr_src0 x) itr_tgt0>>),
          P f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0))
      (TAKER: forall
          f_src f_tgt
          X itr_src0 ktr_tgt0
          (TAKER: True)
          (SIM: exists x, <<SIM: _simg r RR f_src true itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src true itr_src0 (ktr_tgt0 x)>>),
          P f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0))
      (PROGRESS: forall
          f_src f_tgt
          itr_src itr_tgt
          (SIM: r _ _ RR false false itr_src itr_tgt)
          (SRC: f_src = true)
          (TGT: f_tgt = true),
          P f_src f_tgt itr_src itr_tgt)
  :
    forall f_src f_tgt itr_src itr_tgt
           (SIM: _simg r RR f_src f_tgt itr_src itr_tgt),
      P f_src f_tgt itr_src itr_tgt.
Proof.
  fix IH 5. i. inv SIM.
  { eapply RET; eauto. }
  { eapply SYSCALL; eauto. }
  { eapply TAUL; eauto. }
  { eapply TAUR; eauto. }
  { eapply CHOOSEL; eauto. des. esplits; eauto. }
  { eapply CHOOSER; eauto. }
  { eapply TAKEL; eauto. }
  { eapply TAKER; eauto. des. esplits; eauto. }
  { eapply PROGRESS; eauto. }
Qed.

Definition simg: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop := paco7 _simg bot7.

Lemma simg_mon: monotone7 _simg.
Proof.
  ii. induction IN using _simg_ind2.
  { econs 1; eauto. }
  { econs 2; eauto. }
  { econs 3; eauto. }
  { econs 4; eauto. }
  { econs 5; eauto. des. esplits; eauto. }
  { econs 6; eauto. i. exploit SIM; eauto. des. i. des. eauto. }
  { econs 7; eauto. i. exploit SIM; eauto. des. i. des. eauto. }
  { econs 8; eauto. des. esplits; eauto. }
  { econs 9; eauto. }
Qed.
Hint Resolve simg_mon: paco.
Hint Resolve cpn7_wcompat: paco.


Inductive simg_indC
          (simg: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (f_src f_tgt: bool): (itree eventE R0) -> (itree eventE R1) -> Prop :=
| simg_indC_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    simg_indC simg RR f_src f_tgt (Ret r_src) (Ret r_tgt)
| simg_indC_syscall
    ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR true true (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    simg_indC simg RR f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)

| simg_indC_tauL
    itr_src0 itr_tgt0
    (TAUL: True)
    (SIM: simg _ _ RR true f_tgt itr_src0 itr_tgt0)
  :
    simg_indC simg RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
| simg_indC_tauR
    itr_src0 itr_tgt0
    (TAUR: True)
    (SIM: simg _ _ RR f_src true itr_src0 itr_tgt0)
  :
    simg_indC simg RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

| simg_indC_chooseL
    X ktr_src0 itr_tgt0
    (CHOOSEL: True)
    (SIM: exists x, simg _ _ RR true f_tgt (ktr_src0 x) itr_tgt0)
  :
    simg_indC simg RR f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
| simg_indC_chooseR
    X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (SIM: forall x, simg _ _ RR f_src true itr_src0 (ktr_tgt0 x))
  :
    simg_indC simg RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

| simg_indC_takeL
    X ktr_src0 itr_tgt0
    (TAKEL: True)
    (SIM: forall x, simg _ _ RR true f_tgt (ktr_src0 x) itr_tgt0)
  :
    simg_indC simg RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)
| simg_indC_takeR
    X itr_src0 ktr_tgt0
    (TAKER: True)
    (SIM: exists x, simg _ _ RR f_src true itr_src0 (ktr_tgt0 x))
  :
    simg_indC simg RR f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0)
.

Lemma simg_indC_mon: monotone7 simg_indC.
Proof.
  ii. inv IN.
  { econs 1; eauto. }
  { econs 2; eauto. }
  { econs 3; eauto. }
  { econs 4; eauto. }
  { econs 5; eauto. des. esplits; eauto. }
  { econs 6; eauto. }
  { econs 7; eauto. }
  { econs 8; eauto. des. esplits; eauto. }
Qed.
Hint Resolve simg_indC_mon: paco.

Lemma simg_indC_spec:
  simg_indC <8= gupaco7 _simg (cpn7 _simg).
Proof.
  eapply wrespect7_uclo; eauto with paco.
  econs; eauto with paco. i. inv PR.
  { econs 1; eauto. }
  { econs 2; eauto. i. eapply rclo7_base. auto. }
  { econs 3; eauto. eapply simg_mon; eauto. i. eapply rclo7_base. auto. }
  { econs 4; eauto. eapply simg_mon; eauto. i. eapply rclo7_base. auto. }
  { des. econs 5; eauto. esplits. eapply simg_mon; eauto. i. eapply rclo7_base; eauto. }
  { econs 6; eauto. i. eapply simg_mon; eauto. i. eapply rclo7_base; eauto. }
  { econs 7; eauto. i. eapply simg_mon; eauto. i. eapply rclo7_base; eauto. }
  { des. econs 8; eauto. esplits. eapply simg_mon; eauto. i. eapply rclo7_base; eauto. }
Qed.

Lemma simg_ind R0 R1 (RR: R0 -> R1 -> Prop)
      (P: bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop)
      (RET: forall
          f_src f_tgt
          r_src r_tgt
          (SIM: RR r_src r_tgt),
          P f_src f_tgt (Ret r_src) (Ret r_tgt))
      (SYSCALL: forall
          f_src f_tgt
          ktr_src0 ktr_tgt0 fn varg rvs
          (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg RR true true (ktr_src0 x_src) (ktr_tgt0 x_tgt)),
          P f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0))
      (TAUL: forall
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUL: True)
          (SIM: simg RR true f_tgt itr_src0 itr_tgt0)
          (IH: P true f_tgt itr_src0 itr_tgt0),
          P f_src f_tgt (tau;; itr_src0) (itr_tgt0))
      (TAUR: forall
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUR: True)
          (SIM: simg RR f_src true itr_src0 itr_tgt0)
          (IH: P f_src true itr_src0 itr_tgt0),
          P f_src f_tgt (itr_src0) (tau;;itr_tgt0))
      (CHOOSEL: forall
          f_src f_tgt
          X ktr_src0 itr_tgt0
          (CHOOSEL: True)
          (SIM: exists x, <<SIM: simg RR true f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P true f_tgt (ktr_src0 x) itr_tgt0>>),
          P f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0))
      (CHOOSER: forall
          f_src f_tgt
          X itr_src0 ktr_tgt0
          (CHOOSER: True)
          (SIM: forall x, <<SIM: simg RR f_src true itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src true itr_src0 (ktr_tgt0 x)>>),
          P f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0))
      (TAKEL: forall
          f_src f_tgt
          X ktr_src0 itr_tgt0
          (TAKEL: True)
          (SIM: forall x, <<SIM: simg RR true f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P true f_tgt (ktr_src0 x) itr_tgt0>>),
          P f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0))
      (TAKER: forall
          f_src f_tgt
          X itr_src0 ktr_tgt0
          (TAKER: True)
          (SIM: exists x, <<SIM: simg RR f_src true itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src true itr_src0 (ktr_tgt0 x)>>),
          P f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0))
      (PROGRESS: forall
          f_src f_tgt
          itr_src itr_tgt
          (SIM: simg RR false false itr_src itr_tgt)
          (SRC: f_src = true)
          (TGT: f_tgt = true),
          P f_src f_tgt itr_src itr_tgt)
  :
    forall f_src f_tgt itr_src itr_tgt
           (SIM: simg RR f_src f_tgt itr_src itr_tgt),
      P f_src f_tgt itr_src itr_tgt.
Proof.
  i. punfold SIM. induction SIM using _simg_ind2; i; clarify.
  { eapply RET; eauto. }
  { eapply SYSCALL; eauto. i. exploit SIM; eauto. i. des. pclearbot. eauto. }
  { eapply TAUL; eauto. pfold. auto. }
  { eapply TAUR; eauto. pfold. auto. }
  { eapply CHOOSEL; eauto. des. esplits; eauto. pfold. auto. }
  { eapply CHOOSER; eauto. i. exploit SIM; eauto. i. des. esplits; eauto. pfold. auto. }
  { eapply TAKEL; eauto. i. exploit SIM; eauto. i. des. esplits; eauto. pfold. auto. }
  { eapply TAKER; eauto. des. esplits; eauto. pfold. auto. }
  { eapply PROGRESS; eauto. pclearbot. auto. }
Qed.

End TY.

Hint Constructors _simg.
Hint Unfold simg.
Hint Resolve simg_mon: paco.
Hint Resolve cpn7_wcompat: paco.

Variant flagC (r: forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| flagC_intro
    f_src0 f_src1 f_tgt0 f_tgt1 R0 R1 (RR: R0 -> R1 -> Prop) itr_src itr_tgt
    (SRC: f_src0 = true -> f_src1 = true)
    (TGT: f_tgt0 = true -> f_tgt1 = true)
    (SIM: r _ _ RR f_src0 f_tgt0 itr_src itr_tgt)
  :
    flagC r RR f_src1 f_tgt1 itr_src itr_tgt
.
Hint Constructors flagC: core.

Lemma flagC_mon
      r1 r2
      (LE: r1 <7= r2)
  :
    flagC r1 <7= flagC r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve flagC_mon: paco.

Lemma flagC_wrespectful: wrespectful7 (_simg) flagC.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  eapply GF in SIM.
  revert x3 x4 SRC TGT. induction SIM using _simg_ind2; i; clarify.
  { econs 1; eauto. }
  { econs 2; eauto. i. eapply rclo7_base; eauto. }
  { econs 3; eauto. }
  { econs 4; eauto. }
  { econs 5; eauto. des. esplits; eauto. }
  { econs 6; eauto. i. exploit SIM; eauto. i. des. eauto. }
  { econs 7; eauto. i. exploit SIM; eauto. i. des. eauto. }
  { econs 8; eauto. des. esplits; eauto. }
  { econs 9; eauto. eapply rclo7_clo_base. econs; eauto. }
Qed.

Lemma flagC_spec: flagC <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply wrespect7_uclo; eauto with paco. eapply flagC_wrespectful.
Qed.

Lemma simg_flag
      r R0 R1 RR itr_src itr_tgt f_src0 f_tgt0 f_src1 f_tgt1
      (SIM: @_simg r R0 R1 RR f_src0 f_tgt0 itr_src itr_tgt)
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
  :
    @_simg r R0 R1 RR f_src1 f_tgt1 itr_src itr_tgt.
Proof.
  revert f_src1 f_tgt1 SRC TGT. induction SIM using _simg_ind2; i.
  { econs 1; eauto. }
  { econs 2; eauto. }
  { econs 3; eauto. }
  { econs 4; eauto. }
  { econs 5; eauto. des. esplits; eauto. }
  { econs 6; eauto. i. exploit SIM; eauto. i. des. eauto. }
  { econs 7; eauto. i. exploit SIM; eauto. i. des. eauto. }
  { econs 8; eauto. des. esplits; eauto. }
  { econs 9; eauto. }
Qed.

Lemma simg_progress_flag R0 R1 RR r g itr_src itr_tgt
      (SIM: gpaco7 _simg (cpn7 _simg) g g R0 R1 RR false false itr_src itr_tgt)
  :
    gpaco7 _simg (cpn7 _simg) r g R0 R1 RR true true itr_src itr_tgt.
Proof.
  gstep. econs; eauto.
Qed.

Lemma simg_flag_down R0 R1 RR r g itr_src itr_tgt f_src f_tgt
      (SIM: gpaco7 _simg (cpn7 _simg) r g R0 R1 RR false false itr_src itr_tgt)
  :
    gpaco7 _simg (cpn7 _simg) r g R0 R1 RR f_src f_tgt itr_src itr_tgt.
Proof.
  guclo flagC_spec. econs; [..|eauto]; ss.
Qed.

Lemma simg_bot_flag_up R0 R1 RR st_src st_tgt f_src f_tgt
      (SIM: @simg R0 R1 RR true true st_src st_tgt)
  :
    simg RR f_src f_tgt st_src st_tgt.
Proof.
  ginit. remember true in SIM at 1. remember true in SIM at 1.
  clear Heqb Heqb0. revert st_src st_tgt f_src f_tgt b b0 SIM.
  gcofix CIH. i. revert f_src f_tgt.
  induction SIM using simg_ind.
  { guclo simg_indC_spec. econs 1; eauto. }
  { gstep. econs 2; eauto. i. gbase. eapply CIH; eauto. }
  { guclo simg_indC_spec. econs 3; eauto. }
  { guclo simg_indC_spec. econs 4; eauto. }
  { guclo simg_indC_spec. econs 5; eauto. des. esplits; eauto. }
  { guclo simg_indC_spec. econs 6; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
  { guclo simg_indC_spec. econs 7; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
  { guclo simg_indC_spec. econs 8; eauto. des. esplits; eauto. }
  { i. eapply simg_flag_down. gfinal. right.
    eapply paco7_mon; eauto. ss.
  }
Qed.


Variant bindR (r s: forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| bindR_intro
    f_src f_tgt

    R0 R1 RR
    (i_src: itree eventE R0) (i_tgt: itree eventE R1)
    (SIM: r _ _ RR f_src f_tgt i_src i_tgt)

    S0 S1 SS
    (k_src: ktree eventE R0 S0) (k_tgt: ktree eventE R1 S1)
    (SIMK: forall vret_src vret_tgt (SIM: RR vret_src vret_tgt), s _ _ SS false false (k_src vret_src) (k_tgt vret_tgt))
  :
    bindR r s SS f_src f_tgt (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
.

Hint Constructors bindR: core.

Lemma bindR_mon
      r1 r2 s1 s2
      (LEr: r1 <7= r2) (LEs: s1 <7= s2)
  :
    bindR r1 s1 <7= bindR r2 s2
.
Proof. ii. destruct PR; econs; et. Qed.

Definition bindC r := bindR r r.
Hint Unfold bindC: core.



Lemma bindC_wrespectful: wrespectful7 (_simg) bindC.
Proof.
  econs.
  { ii. eapply bindR_mon; eauto. }
  i. inv PR. csc. eapply GF in SIM.
  revert k_src k_tgt SIMK. induction SIM using _simg_ind2; i.
  { irw. hexploit SIMK; eauto. i. eapply GF in H.
    eapply simg_mon; eauto. eapply simg_flag.
     { eapply simg_mon; eauto. i. eapply rclo7_base. auto. }
    { ss. }
    { ss. }
  }
  { rewrite ! bind_bind. econs; eauto. ii.
    { econs 2; eauto with paco. econs; eauto with paco. }
  }
  { rewrite ! bind_tau. econs; eauto. }
  { rewrite ! bind_tau. econs; eauto. }
  { rewrite ! bind_bind. econs; eauto. des. esplits; et. }
  { rewrite ! bind_bind. econs; eauto. i. exploit SIM; eauto. i. des. eauto. }
  { rewrite ! bind_bind. econs; eauto. i. exploit SIM; eauto. i. des. eauto. }
  { rewrite ! bind_bind. econs; eauto. des. esplits; et. }
  { clarify. econs; eauto. eapply rclo7_clo_base. econs; eauto. }
Qed.

Lemma bindC_spec: bindC <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply wrespect7_uclo; eauto with paco. eapply bindC_wrespectful.
Qed.



Lemma step_trigger_choose_iff X k itr e
      (STEP: ModSemL.step (trigger (Choose X) >>= k) e itr)
  :
    exists x,
      e = None /\ itr = k x.
Proof.
  inv STEP.
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss.
    unfold trigger in H0. ss. cbn in H0.
    dependent destruction H0. ired. et.  }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
Qed.

Lemma step_trigger_take_iff X k itr e
      (STEP: ModSemL.step (trigger (Take X) >>= k) e itr)
  :
    exists x,
      e = None /\ itr = k x.
Proof.
  inv STEP.
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss.
    unfold trigger in H0. ss. cbn in H0.
    dependent destruction H0. ired. et.  }
  { eapply f_equal with (f:=observe) in H0. ss. }
Qed.

Lemma step_tau_iff itr0 itr1 e
      (STEP: ModSemL.step (Tau itr0) e itr1)
  :
    e = None /\ itr0 = itr1.
Proof.
  inv STEP. et.
Qed.

Lemma step_ret_iff rv itr e
      (STEP: ModSemL.step (Ret rv) e itr)
  :
    False.
Proof.
  inv STEP.
Qed.

Lemma step_trigger_syscall_iff fn args rvs k e itr
      (STEP: ModSemL.step (trigger (Syscall fn args rvs) >>= k) e itr)
  :
    exists rv, itr = k rv /\ e = Some (event_sys fn args rv)
               /\ <<RV: rvs rv>> /\ <<SYS: syscall_sem (event_sys fn args rv)>>.
Proof.
  inv STEP.
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss.
    unfold trigger in H0. ss. cbn in H0.
    dependent destruction H0. ired. et. }
Qed.


Lemma itree_eta_eq E R (itr0 itr1: itree E R)
    (OBSERVE: observe itr0 = observe itr1)
  :
    itr0 = itr1.
Proof.
  rewrite (itree_eta_ itr0).
  rewrite (itree_eta_ itr1).
  rewrite OBSERVE. auto.
Qed.

Lemma step_trigger_choose X k x
  :
    ModSemL.step (trigger (Choose X) >>= k) None (k x).
Proof.
  unfold trigger. ss.
  match goal with
  | [ |- ModSemL.step ?itr _ _] =>
    replace itr with (Subevent.vis (Choose X) k)
  end; ss.
  { econs. }
  { eapply itree_eta_eq. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta_eq. ss. }
Qed.

Lemma step_trigger_take X k x
  :
    ModSemL.step (trigger (Take X) >>= k) None (k x).
Proof.
  unfold trigger. ss.
  match goal with
  | [ |- ModSemL.step ?itr _ _] =>
    replace itr with (Subevent.vis (Take X) k)
  end; ss.
  { econs. }
  { eapply itree_eta_eq. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta_eq. ss. }
Qed.

Lemma step_trigger_syscall fn args (rvs: Any.t -> Prop) k rv
      (RV: rvs rv) (SYS: syscall_sem (event_sys fn args rv))
  :
    ModSemL.step (trigger (Syscall fn args rvs) >>= k) (Some (event_sys fn args rv)) (k rv).
Proof.
  unfold trigger. ss.
  match goal with
  | [ |- ModSemL.step ?itr _ _] =>
    replace itr with (Subevent.vis (Syscall fn args rvs) k)
  end; ss.
  { econs; et. }
  { eapply itree_eta_eq. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta_eq. ss. }
Qed.

Lemma step_tau itr
  :
    ModSemL.step (Tau itr) None itr.
Proof.
  econs.
Qed.

Theorem eutt_simg: forall R RR (u t: itree eventE R) (EUTT: eqit RR true true u t), simg RR false false u t.
Proof.
  i. ginit. revert_until R. gcofix CIH. i.
  punfold EUTT. red in EUTT.
  dependent induction EUTT; try apply simpobs in x; try apply simpobs in x0; try f in x; try f in x0; subst.
  - gstep; econs; eauto.
  - guclo simg_indC_spec. econs; eauto.
    guclo simg_indC_spec. econs; eauto.
    gstep. econs; eauto. gbase. eapply CIH. pclearbot. eauto.
  - rewrite <- ! bind_trigger.
    destruct e.
    + guclo simg_indC_spec. econsr; eauto. i.
      guclo simg_indC_spec. econs; eauto. esplits.
      gstep. econs; eauto. gbase. eapply CIH. pclearbot. eauto.
    + guclo simg_indC_spec. econs; eauto. i.
      guclo simg_indC_spec. econsr; eauto. esplits.
      gstep. econs; eauto. gbase. eapply CIH. pclearbot. eauto.
    + guclo simg_indC_spec. econs; eauto. i. subst.
      gstep. econs; eauto. gbase. eapply CIH. pclearbot. eauto.
  - guclo simg_indC_spec. econs; eauto.
    eapply simg_flag_down.
    eapply IHEUTT; eauto.
  - guclo simg_indC_spec. econs; eauto.
    eapply simg_flag_down.
    eapply IHEUTT; eauto.
Qed.

Ltac simpobs_all :=
  repeat match goal with
         | [H: VisF _ _ = _ |- _ ] => apply simpobs in H; f in H
         | [H: RetF _ = _ |- _ ] => apply simpobs in H; f in H
         | [H: TauF _ = _ |- _ ] => apply simpobs in H; f in H
         | [H: _ = VisF _ _ |- _ ] => sym in H; apply simpobs in H; f in H
         | [H: _ = RetF _ |- _ ] => sym in H; apply simpobs in H; f in H
         | [H: _ = TauF _ |- _ ] => sym in H; apply simpobs in H; f in H
         end;
  subst.

Structure grespectful clo : Prop :=
  grespect_intro {
      grespect_mon: monotone7 clo;
      grespect_respect :
      forall l r
             (LE: l <7= r)
             (GF: l <7= @_simg r),
        clo l <7= gpaco7 _simg (cpn7 _simg) bot7 (rclo7 (clo \8/ gupaco7 _simg (cpn7 _simg)) r);
    }.

Lemma grespect_uclo clo
      (RESPECT: grespectful clo)
  :
  clo <8= gupaco7 (_simg) (cpn7 _simg).
Proof.
  eapply grespect7_uclo; eauto with paco.
  econs.
  { eapply RESPECT. }
  i. hexploit grespect_respect.
  { eauto. }
  { eapply LE. }
  { eapply GF. }
  { eauto. }
  i. inv H. eapply rclo7_mon.
  { eauto. }
  i. ss. des; ss. eapply _paco7_unfold in PR0.
  2:{ ii. eapply simg_mon; [eapply PR1|]. i. eapply rclo7_mon; eauto. }
  ss. eapply simg_mon.
  { eapply PR0; eauto. }
  i. eapply rclo7_clo. right. econs.
  eapply rclo7_mon; eauto. i. inv PR2.
  { left. eapply paco7_mon; eauto. i. ss. des; ss.
    left. auto. }
  { des; ss. right. auto. }
Qed.

Lemma euttge_inv
      E R (itr0 itr1: itree E R)
      (TAU: (tau;; itr0) ≳ (tau;; itr1))
  :
  <<TAU: itr0 ≳ itr1>>.
Proof.
  eapply eqit_Tau. eauto.
Qed.

Lemma euttge_tau_inv
      E R (itr0 itr1: itree E R)
      (TAU: itr0 ≳ (tau;; itr1))
  :
  exists itr0', <<EQ: itr0 = tau;; itr0'>> /\ <<TAU: itr0' ≳ itr1>>.
Proof.
  punfold TAU. r in TAU. dup TAU. dependent induction TAU; simpobs_all.
  - pclearbot. esplits; eauto.
  - esplits; eauto. eapply euttge_inv; eauto.
  - rr in CHECK. ss.
Qed.



Variant _eutt0C (r: forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| _eutt0C_intro
    f_src0 f_tgt0 R0 R1 (RR: R0 -> R1 -> Prop) itr_src1 itr_src0 itr_tgt0 (* itr_tgt1 *)
    (SIM: r _ _ RR f_src0 f_tgt0 itr_src1 itr_tgt0)
    (LEFT: itr_src0 ≳ itr_src1)
  :
    _eutt0C r RR f_src0 f_tgt0 itr_src0 itr_tgt0
.
Hint Constructors _eutt0C: core.

Lemma _eutt0C_mon
      r1 r2
      (LE: r1 <7= r2)
  :
    _eutt0C r1 <7= _eutt0C r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve _eutt0C_mon: paco.

Lemma _eutt0C_grespectful: grespectful _eutt0C.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  eapply GF in SIM.
  rename x2 into RR. rename x5 into itr_src0. rename x6 into itr_tgt0.
  (* revert_until RR. gcofix CIH. i. *)
  revert_until SIM. revert itr_src0. induction SIM using _simg_ind2; i; clarify.
  { punfold LEFT. red in LEFT.
    revert SIM. dependent induction LEFT; i; simpobs_all; clarify.
    - gstep. econs; eauto.
    - guclo simg_indC_spec. econs; eauto. guclo flagC_spec.
  }
  { punfold LEFT. red in LEFT.
    revert SIM. dependent induction LEFT; i; des_ifs; simpl_existTs; subst; simpobs_all.
    - rewrite bind_trigger in Heq. clarify. simpl_existTs. subst. rewrite <- bind_trigger.
      gstep. econs; eauto. i. subst. gbase. (* eapply CIH0. *) eapply rclo7_clo. left. econs; cycle 1.
      { instantiate (1:=ktr_src0 x_tgt). rr in REL. pclearbot. eauto. }
      eapply rclo7_base. eauto.
    - guclo simg_indC_spec. econs; eauto. guclo flagC_spec.
  }
  { eapply euttge_tau_inv in LEFT. des. subst.
    guclo simg_indC_spec. econs; eauto.
  }
  { guclo simg_indC_spec. econs; eauto. }
  { des.
    punfold LEFT. red in LEFT.
    dependent induction LEFT; i; des_ifs; simpl_existTs; subst; simpobs_all.
    - rewrite bind_trigger in Heq. clarify. simpl_existTs. subst. rewrite <- bind_trigger.
      guclo simg_indC_spec. econs; eauto. esplits; eauto.
      eapply IH. rr in REL. pclearbot. eauto.
    - guclo simg_indC_spec. econs; eauto. guclo flagC_spec.
  }
  { guclo simg_indC_spec. econs; eauto. i. eapply SIM. eauto. }
  { punfold LEFT. red in LEFT.
    dependent induction LEFT; i; des_ifs; simpl_existTs; subst; simpobs_all.
    - rewrite bind_trigger in Heq. clarify. simpl_existTs. subst. rewrite <- bind_trigger.
      guclo simg_indC_spec. econs; eauto. i.
      eapply SIM. rr in REL. pclearbot. eauto.
    - guclo simg_indC_spec. econs; eauto. guclo flagC_spec.
  }
  { des. guclo simg_indC_spec. econs; eauto. }
  { gstep. econs; eauto. gbase. eapply rclo7_clo. eauto with paco. }
Qed.

Lemma _eutt0C_spec: _eutt0C <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply grespect_uclo; eauto with paco. eapply _eutt0C_grespectful.
Qed.

Variant _eutt1C (r: forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| _eutt1C_intro
    f_src0 f_tgt0 R0 R1 (RR: R0 -> R1 -> Prop) itr_tgt1 itr_src0 itr_tgt0
    (SIM: r _ _ RR f_src0 f_tgt0 itr_src0 itr_tgt1)
    (RIGHT: itr_tgt0 ≳ itr_tgt1)
  :
    _eutt1C r RR f_src0 f_tgt0 itr_src0 itr_tgt0
.
Hint Constructors _eutt1C: core.

Lemma _eutt1C_mon
      r1 r2
      (LE: r1 <7= r2)
  :
    _eutt1C r1 <7= _eutt1C r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve _eutt1C_mon: paco.

Lemma _eutt1C_grespectful: grespectful _eutt1C.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  eapply GF in SIM.
  rename x2 into RR. rename x5 into itr_src0. rename x6 into itr_tgt0.
  (* revert_until RR. gcofix CIH. i. *)
  revert_until SIM. revert itr_tgt0. induction SIM using _simg_ind2; i; clarify.
  { punfold RIGHT. red in RIGHT.
    revert SIM. dependent induction RIGHT; i; simpobs_all; clarify.
    - gstep. econs; eauto.
    - guclo simg_indC_spec. econs; eauto. guclo flagC_spec.
  }
  { punfold RIGHT. red in RIGHT.
    revert SIM. dependent induction RIGHT; i; des_ifs; simpl_existTs; subst; simpobs_all.
    - rewrite bind_trigger in Heq. clarify. simpl_existTs. subst. rewrite <- bind_trigger.
      gstep. econs; eauto. i. subst. gbase. (* eapply CIH0. *) eapply rclo7_clo. left. econs; cycle 1.
      { instantiate (1:=ktr_tgt0 x_tgt). rr in REL. pclearbot. eauto. }
      eapply rclo7_base. eauto.
    - guclo simg_indC_spec. econs; eauto. guclo flagC_spec.
  }
  { guclo simg_indC_spec. econs; eauto. }
  { eapply euttge_tau_inv in RIGHT. des. subst.
    guclo simg_indC_spec. econs; eauto.
  }
  { des. guclo simg_indC_spec. econs; eauto. }
  { punfold RIGHT. red in RIGHT.
    dependent induction RIGHT; i; des_ifs; simpl_existTs; subst; simpobs_all.
    - rewrite bind_trigger in Heq. clarify. simpl_existTs. subst. rewrite <- bind_trigger.
      guclo simg_indC_spec. econs; eauto. esplits; eauto.
      eapply SIM. rr in REL. pclearbot. eauto.
    - guclo simg_indC_spec. econs; eauto. guclo flagC_spec.
  }
  { guclo simg_indC_spec. econs; eauto. i. eapply SIM. eauto. }
  { des.
    punfold RIGHT. red in RIGHT.
    dependent induction RIGHT; i; des_ifs; simpl_existTs; subst; simpobs_all.
    - rewrite bind_trigger in Heq. clarify. simpl_existTs. subst. rewrite <- bind_trigger.
      guclo simg_indC_spec. econs; eauto. esplits; eauto.
      eapply IH. rr in REL. pclearbot. eauto.
    - guclo simg_indC_spec. econs; eauto. guclo flagC_spec.
  }
  { gstep. econs; eauto. gbase. eapply rclo7_clo. eauto with paco. }
Qed.

Lemma _eutt1C_spec: _eutt1C <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply grespect_uclo; eauto with paco. eapply _eutt1C_grespectful.
Qed.

Variant euttC (r: forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| euttC_intro
    f_src0 f_tgt0 R0 R1 (RR: R0 -> R1 -> Prop) itr_src1 itr_tgt1 itr_src0 itr_tgt0
    (SIM: r _ _ RR f_src0 f_tgt0 itr_src1 itr_tgt1)
    (LEFT: itr_src0 ≳ itr_src1)
    (RIGHT: itr_tgt0 ≳ itr_tgt1)
  :
    euttC r RR f_src0 f_tgt0 itr_src0 itr_tgt0
.
Hint Constructors euttC: core.

Lemma euttC_mon
      r1 r2
      (LE: r1 <7= r2)
  :
    euttC r1 <7= euttC r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve euttC_mon: paco.

Lemma euttC_grespectful: grespectful euttC.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  eapply GF in SIM.
  rename x2 into RR. rename x5 into itr_src0. rename x6 into itr_tgt0.

  guclo _eutt0C_spec. econs; eauto.
  guclo _eutt1C_spec. econs; eauto.
  gfinal. right. pfold. eapply simg_mon; eauto. ii. right. eapply rclo7_base. eauto.
Qed.

Lemma euttC_spec: euttC <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply grespect_uclo; eauto with paco. eapply euttC_grespectful.
Qed.

(* Lemma simg_tau_split_l *)
(*         R *)
(*         f0 f1 i0 i1 *)
(*         (SIM: simg (@eq R) f0 f1 (tau;; i0) i1) *)
(*   : *)
(*   exists hd tl, i1 = hd >>= tl /\  *)
(*   simg eq true f1 i0 i1 *)
(* . *)
(* Proof. *)
(* Qed. *)

(* Notation simgc := (simg eq false false). *)

Lemma simg_tau_inv_l
        R
        f0 f1 i0 i1
        (SIM: simg (@eq R) f0 f1 (tau;; i0) i1)
  :
  simg eq f0 f1 i0 i1
.
Proof.
  ginit. revert_until R. gcofix CIH. i.
  remember (tau;; i0) as tmp. revert i0 Heqtmp.
  induction SIM using simg_ind; intros ? EQ; irw in EQ; csc.
  - gfinal. right.
    assert(T: simg eq true true i0 itr_tgt0).
    { ginit. guclo flagC_spec. }
    eapply simg_bot_flag_up in T.
    eapply paco7_mon; et. i; ss.
  - guclo simg_indC_spec. econs; eauto.
  - guclo simg_indC_spec. econs; eauto. i. specialize (SIM x). des. eapply IH; ss.
  - guclo simg_indC_spec. econs; eauto. des. esplits; eauto.
  - gstep. econs; eauto. gbase. eapply CIH; ss.
Qed.

Lemma simg_tau_choose_l
        R X
        f0 f1 k0 i1
        (SIM: simg (@eq R) f0 f1 (trigger (Choose X) >>= k0) i1)
  :
  exists x, simg eq f0 f1 (k0 x) i1
.
Proof.
  (* ginit. revert_until R. gcofix CIH. i. *)
  remember (` x : _ <- trigger (Choose X);; k0 x) as tmp. revert k0 Heqtmp.
  induction SIM using simg_ind; intros ? EQ; irw in EQ; csc.
  - exploit IHSIM; et. { irw; ss. } i; des. esplits; et.
    ginit. guclo simg_indC_spec. econs; et. gfinal. right. eapply paco7_mon; et.
  - assert(ktr_src0 = k0) by eauto. subst. clear_tac.
    des. esplits; et.
    assert(T: simg eq true true (k0 x) itr_tgt0).
    { ginit. guclo flagC_spec. }
    eapply simg_bot_flag_up in T; et.
  -
    (** yeah the lemma seems to be wrong... without future-sim **)
Abort.

Lemma simg_tau_take_l
        R X
        f0 f1 k0 i1
        (SIM: simg (@eq R) f0 f1 (trigger (Take X) >>= k0) i1)
  :
  forall x, simg eq f0 f1 (k0 x) i1
.
Proof.
  i. ginit. revert_until R. gcofix CIH. i.
  remember (` x : _ <- trigger (Take X);; k0 x) as tmp. revert k0 Heqtmp.
  induction SIM using simg_ind; intros ? EQ; irw in EQ; csc.
  - exploit IHSIM; et. { irw; ss. } i; des.
    guclo simg_indC_spec. econs; et.
  - guclo simg_indC_spec. econs; et. i. eapply SIM. irw; ss.
  - assert(ktr_src0 = k0) by eauto. subst. clear_tac.
    spc SIM. des.
    assert(T: simg eq true true (k0 x) itr_tgt0).
    { ginit. guclo flagC_spec. }
    eapply simg_bot_flag_up in T; et.
    gfinal. right. eapply paco7_mon; et. i; ss.
  - des.
    guclo simg_indC_spec. econs; et. esplits; et. eapply IH. irw; ss.
  - gstep. econs; et. gbase. eapply CIH; et. rewrite <- bind_trigger in *. ss.
Qed.

Lemma simg_tau_inv_r
        R
        f0 f1 i0 i1
        (SIM: simg (@eq R) f0 f1 (i0) (tau;; i1))
  :
  simg eq f0 f1 i0 i1
.
Proof.
  ginit. revert_until R. gcofix CIH. i.
  remember (tau;; i1) as tmp. revert i1 Heqtmp.
  induction SIM using simg_ind; intros ? EQ; irw in EQ; csc.
  - guclo simg_indC_spec. econs; eauto.
  - gfinal. right.
    assert(T: simg eq true true itr_src0 i1).
    { ginit. guclo flagC_spec. }
    eapply simg_bot_flag_up in T.
    eapply paco7_mon; et. i; ss.
  - guclo simg_indC_spec. econs; eauto. des. esplits; eauto.
  - guclo simg_indC_spec. econs; eauto. i. specialize (SIM x). des. eapply IH; ss.
  - gstep. econs; eauto. gbase. eapply CIH; ss.
Qed.

Lemma simg_tau_choose_r
        R X
        f0 f1 k1 i0
        (SIM: simg (@eq R) f0 f1 i0 (trigger (Choose X) >>= k1))
  :
  forall x, simg eq f0 f1 i0 (k1 x)
.
Proof.
  i. ginit. revert_until R. gcofix CIH. i.
  remember (` x : _ <- trigger (Choose X);; k1 x) as tmp. revert k1 Heqtmp.
  induction SIM using simg_ind; intros ? EQ; irw in EQ; csc.
  - exploit IHSIM; et. { irw; ss. } i; des.
    guclo simg_indC_spec. econs; et.
  - rename X0 into Y. des. rename x0 into y. guclo simg_indC_spec. econs; et. esplits; et. eapply IH. irw; ss.
  - assert(ktr_tgt0 = k1) by eauto. subst. clear_tac.
    spc SIM. des.
    assert(T: simg eq true true itr_src0 (k1 x)).
    { ginit. guclo flagC_spec. }
    eapply simg_bot_flag_up in T; et.
    gfinal. right. eapply paco7_mon; et. i; ss.
  - guclo simg_indC_spec. econs; et. i. eapply SIM. irw; ss.
  - gstep. econs; et. gbase. eapply CIH; et. rewrite <- bind_trigger in *. ss.
Qed.

Lemma simg_tau_take_r
        R X
        f0 f1 k0 i1
        (SIM: simg (@eq R) f0 f1 (trigger (Take X) >>= k0) i1)
  :
  exists x, simg eq f0 f1 (k0 x) i1
.
Proof.
Abort.

Lemma trans
  R
  (itr0 itr1 itr2: itree eventE R)
  (SIM0: simg eq false false itr0 itr1)
  (SIM1: simg eq false false itr1 itr2)
  :
  <<SIM: simg eq false false itr0 itr2>>
.
Proof.
  ginit.
  revert_until R.
  gcofix CIH.
  i.
  (* remember false as tmp0 in SIM0 at 1. *)
  (* remember false as tmp1 in SIM0 at 1. *)
  (* revert Heqtmp0 Heqtmp1. *)

  revert SIM1. revert itr2.
  induction SIM0 using simg_ind; i; clarify.
  (* induction SIM0 using simg_ind. clarify. *)
  - gfinal. right. eapply paco7_mon.
    { eapply simg_bot_flag_up; et. ginit. guclo flagC_spec. }
    i; ss.
  - remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp.
    revert Heqtmp.
    induction SIM1 using simg_ind; intros EQ; try irw in EQ; csc.
    (* remember false as tmp0 in SIM1 at 1. *)
    (* remember false as tmp1 in SIM1 at 1. *)
    (* remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. *)
    (* revert Heqtmp Heqtmp0 Heqtmp1. *)
    (* induction SIM1 using simg_ind; intros EQ??; try irw in EQ; csc. *)
    + change (fun x : Any.t => ktr_src1 x) with ktr_src1 in *.
      change (fun x : Any.t => ktr_tgt0 x) with ktr_tgt0 in *.
      subst.
      gstep. econs; eauto. gstep. econs; eauto. subst. gbase.
Abort.

Lemma trans
  R
  f0 f1
  (itr0 itr1 itr2: itree eventE R)
  (SIM0: simg eq f0 f1 itr0 itr1)
  (SIM1: simg eq false false itr1 itr2)
  :
  <<SIM: simg eq f0 f1 itr0 itr2>>
.
Proof.
  ginit.
  revert_until R.
  gcofix CIH.
  i.
  (* remember false as tmp0 in SIM0 at 1. *)
  (* remember false as tmp1 in SIM0 at 1. *)
  (* revert Heqtmp0 Heqtmp1. *)

  revert SIM1. revert itr2.
  induction SIM0 using simg_ind; i; clarify.
  (* induction SIM0 using simg_ind. clarify. *)
  - gfinal. right. eapply paco7_mon.
    { eapply simg_bot_flag_up; et. ginit. guclo flagC_spec. }
    i; ss.
  - remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp.
    revert Heqtmp.
    induction SIM1 using simg_ind; intros EQ; try irw in EQ; csc.
    (* remember false as tmp0 in SIM1 at 1. *)
    (* remember false as tmp1 in SIM1 at 1. *)
    (* remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. *)
    (* revert Heqtmp Heqtmp0 Heqtmp1. *)
    (* induction SIM1 using simg_ind; intros EQ??; try irw in EQ; csc. *)
    + change (fun x : Any.t => ktr_src1 x) with ktr_src1 in *.
      change (fun x : Any.t => ktr_tgt0 x) with ktr_tgt0 in *.
      subst.
      gstep. econs; eauto. gstep. econs; eauto. subst. gbase. eapply CIH; et.
      { eapply simg_bot_flag_up; et. }
      { eapply simg_bot_flag_up; et. }
    + guclo simg_indC_spec. econs; eauto. guclo flagC_spec. econs; try apply IHSIM1; ss.
      { i. eapply CIH; et. eapply simg_bot_flag_up; et. } irw; ss.
    + guclo simg_indC_spec. econs; eauto. i. guclo flagC_spec. econs; try apply SIM0; ss.
      { i. eapply CIH; et. eapply simg_bot_flag_up; et. } irw; ss.
    + guclo simg_indC_spec. econs; eauto. des. esplits; et. guclo flagC_spec. econs; try eapply IH; ss.
      { i. eapply CIH; et. eapply simg_bot_flag_up; et. } irw; ss.
    +
Abort.

Lemma trans
  R
  f0 f1 f2 f3 f4 f5
  (itr0 itr1 itr2: itree eventE R)
  (SIM0: simg eq f0 f1 itr0 itr1)
  (SIM1: simg eq f2 f3 itr1 itr2)
  :
  <<SIM: simg eq f4 f5 itr0 itr2>>
.
Proof.
  ginit.
  revert_until R.
  gcofix CIH.
  i.
  (* remember false as tmp0 in SIM0 at 1. *)
  (* remember false as tmp1 in SIM0 at 1. *)
  (* revert Heqtmp0 Heqtmp1. *)

  revert SIM1. revert itr2.
  induction SIM0 using simg_ind; i; clarify.
  (* induction SIM0 using simg_ind. clarify. *)
  - gfinal. right. eapply paco7_mon.
    { eapply simg_bot_flag_up; et. ginit. guclo flagC_spec. }
    i; ss.
  - remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp.
    revert Heqtmp.
    induction SIM1 using simg_ind; intros EQ; try irw in EQ; csc.
    (* remember false as tmp0 in SIM1 at 1. *)
    (* remember false as tmp1 in SIM1 at 1. *)
    (* remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. *)
    (* revert Heqtmp Heqtmp0 Heqtmp1. *)
    (* induction SIM1 using simg_ind; intros EQ??; try irw in EQ; csc. *)
    + change (fun x : Any.t => ktr_src1 x) with ktr_src1 in *.
      change (fun x : Any.t => ktr_tgt0 x) with ktr_tgt0 in *.
      subst.
      gstep. econs; eauto. gstep. econs; eauto. subst. gbase. eapply CIH; et.
    + guclo simg_indC_spec. econs; eauto. guclo flagC_spec. econs; try apply IHSIM1; ss. irw; ss.
    + guclo simg_indC_spec. econs; eauto. i. guclo flagC_spec. econs; try apply SIM0; ss. irw; ss.
    + guclo simg_indC_spec. econs; eauto. des. esplits; et. guclo flagC_spec. econs; try eapply IH; ss. irw; ss.
    +
Abort.
  (* R : Type *)
  (* r : forall x x0 : Type, (x -> x0 -> Prop) -> bool -> bool -> itree eventE x -> itree eventE x0 -> Prop *)
  (* CIH : forall (f0 f1 f2 f3 f4 f5 : bool) (itr0 itr1 itr2 : itree eventE R), *)
  (*       simg eq f0 f1 itr0 itr1 -> simg eq f2 f3 itr1 itr2 -> r R R eq f4 f5 itr0 itr2 *)
  (* f4, f5, f_src, f_tgt : bool *)
  (* ktr_src0, ktr_tgt0 : Any.t -> itree eventE R *)
  (* fn : string *)
  (* varg : Any.t *)
  (* rvs : Any.t -> Prop *)
  (* SIM : forall x_src x_tgt : Any.t, x_src = x_tgt -> simg eq true true (ktr_src0 x_src) (ktr_tgt0 x_tgt) *)
  (* itr_tgt : itree eventE R *)
  (* SIM1 : simg eq false false (vis (Syscall fn varg rvs) (fun x : Any.t => ktr_tgt0 x)) itr_tgt *)
  (* ============================ *)
  (* gpaco7 _simg (cpn7 _simg) bot7 r R R eq f4 f5 (` x : _ <- trigger (Syscall fn varg rvs);; ktr_src0 x) itr_tgt *)


Lemma trans
  R
  f0 f1 f2 f3
  (itr0 itr1 itr2: itree eventE R)
  (SIM0: simg eq f0 f1 itr0 itr1)
  (SIM1: simg eq f2 f3 itr1 itr2)
  :
  <<SIM: simg eq f0 f1 itr0 itr2>>
.
Proof.
  ginit.
  revert_until R.
  gcofix CIH.
  i.
  (* remember false as tmp0 in SIM0 at 1. *)
  (* remember false as tmp1 in SIM0 at 1. *)
  (* revert Heqtmp0 Heqtmp1. *)

  revert SIM1. revert itr2.
  induction SIM0 using simg_ind; i; clarify.
  (* induction SIM0 using simg_ind. clarify. *)
  - gfinal. right. eapply paco7_mon.
    { eapply simg_bot_flag_up; et. ginit. guclo flagC_spec. }
    i; ss.
  - remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp.
    revert Heqtmp.
    induction SIM1 using simg_ind; intros EQ; try irw in EQ; csc.
    (* remember false as tmp0 in SIM1 at 1. *)
    (* remember false as tmp1 in SIM1 at 1. *)
    (* remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. *)
    (* revert Heqtmp Heqtmp0 Heqtmp1. *)
    (* induction SIM1 using simg_ind; intros EQ??; try irw in EQ; csc. *)
    + change (fun x : Any.t => ktr_src1 x) with ktr_src1 in *.
      change (fun x : Any.t => ktr_tgt0 x) with ktr_tgt0 in *.
      subst.
      gstep. econs; eauto. gstep. econs; eauto. subst. gbase. eapply CIH; et.
      eapply simg_bot_flag_up; et.
    + guclo simg_indC_spec. econs; eauto. guclo flagC_spec. econs; try apply IHSIM1; ss. irw; ss.
    + guclo simg_indC_spec. econs; eauto. i. guclo flagC_spec. econs; try apply SIM0; ss. irw; ss.
    + guclo simg_indC_spec. econs; eauto. des. esplits; et. guclo flagC_spec. econs; try eapply IH; ss. irw; ss.
    +
Abort.
  (* R : Type *)
  (* r : forall x x0 : Type, (x -> x0 -> Prop) -> bool -> bool -> itree eventE x -> itree eventE x0 -> Prop *)
  (* CIH : forall (f0 f1 f2 f3 : bool) (itr0 itr1 itr2 : itree eventE R), *)
  (*       simg eq f0 f1 itr0 itr1 -> simg eq f2 f3 itr1 itr2 -> r R R eq f0 f1 itr0 itr2 *)
  (* f_src, f_tgt : bool *)
  (* ktr_src0, ktr_tgt0 : Any.t -> itree eventE R *)
  (* fn : string *)
  (* varg : Any.t *)
  (* rvs : Any.t -> Prop *)
  (* SIM : forall x_src x_tgt : Any.t, x_src = x_tgt -> simg eq true true (ktr_src0 x_src) (ktr_tgt0 x_tgt) *)
  (* itr_tgt : itree eventE R *)
  (* SIM1 : simg eq false false (vis (Syscall fn varg rvs) (fun x : Any.t => ktr_tgt0 x)) itr_tgt *)
  (* ============================ *)
  (* gpaco7 _simg (cpn7 _simg) bot7 r R R eq f_src f_tgt (` x : _ <- trigger (Syscall fn varg rvs);; ktr_src0 x) itr_tgt *)


Lemma trans
  R
  f0 f1
  (itr0 itr1 itr2: itree eventE R)
  (SIM0: simg eq f0 f1 itr0 itr1)
  (SIM1: simg eq f0 f1 itr1 itr2)
  :
  <<SIM: simg eq f0 f1 itr0 itr2>>
.
Proof.
  ginit.
  revert_until R.
  gcofix CIH.
  i.
  (* remember false as tmp0 in SIM0 at 1. *)
  (* remember false as tmp1 in SIM0 at 1. *)
  (* revert Heqtmp0 Heqtmp1. *)

  revert SIM1. revert itr2.
  induction SIM0 using simg_ind; i; clarify.
  (* induction SIM0 using simg_ind. clarify. *)
  - gfinal. right. eapply paco7_mon.
    { eapply simg_bot_flag_up; et. ginit. guclo flagC_spec. }
    i; ss.
  - remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp.
    revert Heqtmp.
    induction SIM1 using simg_ind; intros EQ; try irw in EQ; csc.
    (* remember false as tmp0 in SIM1 at 1. *)
    (* remember false as tmp1 in SIM1 at 1. *)
    (* remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. *)
    (* revert Heqtmp Heqtmp0 Heqtmp1. *)
    (* induction SIM1 using simg_ind; intros EQ??; try irw in EQ; csc. *)
    + change (fun x : Any.t => ktr_src1 x) with ktr_src1 in *.
      change (fun x : Any.t => ktr_tgt0 x) with ktr_tgt0 in *.
      subst.
      gstep. econs; eauto. gstep. econs; eauto. subst. gbase. eapply CIH; et.
      { eapply simg_bot_flag_up; et. }
      { eapply simg_bot_flag_up; et. }
    + guclo simg_indC_spec. econs; eauto. guclo flagC_spec. econs; try apply IHSIM1; ss. irw; ss.
    + guclo simg_indC_spec. econs; eauto. i. guclo flagC_spec. econs; try apply SIM0; ss. irw; ss.
    + guclo simg_indC_spec. econs; eauto. des. esplits; et. guclo flagC_spec. econs; try eapply IH; ss. irw; ss.
    + gstep. econs; eauto. gbase. eapply CIH; et. rewrite <- bind_trigger. pstep. econs; eauto.
      i. left. eapply SIM; et.
  - guclo simg_indC_spec. econs; eauto. eapply IHSIM0; et. eapply simg_bot_flag_up; et. ginit. guclo flagC_spec.
  -
Abort.
  (* R : Type *)
  (* r : forall x x0 : Type, (x -> x0 -> Prop) -> bool -> bool -> itree eventE x -> itree eventE x0 -> Prop *)
  (* CIH : forall (f0 f1 : bool) (itr0 itr1 itr2 : itree eventE R), *)
  (*       simg eq f0 f1 itr0 itr1 -> simg eq f0 f1 itr1 itr2 -> r R R eq f0 f1 itr0 itr2 *)
  (* f_src, f_tgt : bool *)
  (* itr_src0, itr_tgt0 : itree eventE R *)
  (* TAUR : True *)
  (* SIM0 : simg eq f_src true itr_src0 itr_tgt0 *)
  (* IHSIM0 : forall itr2 : itree eventE R, *)
  (*          simg eq f_src true itr_tgt0 itr2 -> gpaco7 _simg (cpn7 _simg) bot7 r R R eq f_src true itr_src0 itr2 *)
  (* itr2 : itree eventE R *)
  (* SIM1 : simg eq f_src f_tgt (tau;; itr_tgt0) itr2 *)
  (* ============================ *)
  (* gpaco7 _simg (cpn7 _simg) bot7 r R R eq f_src f_tgt itr_src0 itr2 *)

Lemma trans
  R
  f0 f1 f2 f3
  (itr0 itr1 itr2: itree eventE R)
  (SIM0: simg eq f0 f1 itr0 itr1)
  (SIM1: simg eq f2 f3 itr1 itr2)
  :
  <<SIM: simg eq (f0 || f2) (f1 || f3) itr0 itr2>>
.
Proof.
  ginit.
  revert_until R.
  gcofix CIH.
  i.
  (* remember false as tmp0 in SIM0 at 1. *)
  (* remember false as tmp1 in SIM0 at 1. *)
  (* revert Heqtmp0 Heqtmp1. *)

  revert SIM1. revert itr2.
  induction SIM0 using simg_ind; i; clarify.
  (* induction SIM0 using simg_ind. clarify. *)
  - gfinal. right. eapply paco7_mon.
    { eapply simg_bot_flag_up; et. ginit. guclo flagC_spec. }
    i; ss.
  - remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp.
    revert Heqtmp.
    induction SIM1 using simg_ind; intros EQ; try irw in EQ; csc.
    (* remember false as tmp0 in SIM1 at 1. *)
    (* remember false as tmp1 in SIM1 at 1. *)
    (* remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. *)
    (* revert Heqtmp Heqtmp0 Heqtmp1. *)
    (* induction SIM1 using simg_ind; intros EQ??; try irw in EQ; csc. *)
    + change (fun x : Any.t => ktr_src1 x) with ktr_src1 in *.
      change (fun x : Any.t => ktr_tgt0 x) with ktr_tgt0 in *.
      subst.
      gstep. econs; eauto. gstep. econs; eauto. subst. gbase. change false with (false || false). eapply CIH; et.
      { eapply simg_bot_flag_up; et. }
      { eapply simg_bot_flag_up; et. }
    + guclo simg_indC_spec. econs; eauto. guclo flagC_spec. econs; try apply IHSIM1; ss. irw; ss.
    + guclo simg_indC_spec. econs; eauto. i. guclo flagC_spec. econs; try apply SIM0; ss. irw; ss.
    + guclo simg_indC_spec. econs; eauto. des. esplits; et. guclo flagC_spec. econs; try eapply IH; ss. irw; ss.
    + bsimpl. gstep. econs; et. gbase. change false with (false || false). eapply CIH; et.
      rewrite <- bind_trigger. ginit. gstep. econs; eauto. i. gfinal. right. eapply SIM; ss.
  - guclo simg_indC_spec. econs; eauto.
  -
Abort.
  (* R : Type *)
  (* r : forall x x0 : Type, (x -> x0 -> Prop) -> bool -> bool -> itree eventE x -> itree eventE x0 -> Prop *)
  (* CIH : forall (f0 f1 f2 f3 : bool) (itr0 itr1 itr2 : itree eventE R), *)
  (*       simg eq f0 f1 itr0 itr1 -> simg eq f2 f3 itr1 itr2 -> r R R eq (f0 || f2) (f1 || f3) itr0 itr2 *)
  (* f2, f3, f_src, f_tgt : bool *)
  (* itr_src0, itr_tgt0 : itree eventE R *)
  (* TAUR : True *)
  (* SIM0 : simg eq f_src true itr_src0 itr_tgt0 *)
  (* IHSIM0 : forall itr2 : itree eventE R, *)
  (*          simg eq f2 f3 itr_tgt0 itr2 -> gpaco7 _simg (cpn7 _simg) bot7 r R R eq (f_src || f2) (true || f3) itr_src0 itr2 *)
  (* itr2 : itree eventE R *)
  (* SIM1 : simg eq f2 f3 (tau;; itr_tgt0) itr2 *)
  (* ============================ *)
  (* gpaco7 _simg (cpn7 _simg) bot7 r R R eq (f_src || f2) (f_tgt || f3) itr_src0 itr2 *)





(* Lemma simg_tau_inv_l *)
(*         R *)
(*         f0 f1 f2 i0 i1 *)
(*         (SIM: ((f0 = false /\ f1 = false) \/ f1 = f2) /\ simg (@eq R) f0 f1 (tau;; i0) i1) *)
(*   : *)
(*   simg eq true f2 i0 i1 *)
(* . *)
(* Proof. *)
(*   ginit. revert_until R. gcofix CIH. i. *)
(*   remember (tau;; i0) as tmp. revert i0 Heqtmp. *)
(*   induction SIM0 using simg_ind; intros ? EQ; irw in EQ; csc. *)
(*   - des. *)
(*     + subst. gfinal. right. eapply paco7_mon; et. i; ss. *)
(*   - guclo simg_indC_spec. econs; eauto. *)
(*   - guclo simg_indC_spec. econs; eauto. i. specialize (SIM x). des. eapply IH; ss. *)
(*   - guclo simg_indC_spec. econs; eauto. des. esplits; eauto. *)
(*   - remember (tau;; i0) as tmp. revert i0 Heqtmp. *)
(*     remember false as tmp2. revert Heqtmp2. *)
(*     induction SIM using simg_ind; intros ? ? EQ; irw in EQ; csc. *)
(*     + gstep. econs; eauto. gbase. gfinal. right. eapply paco7_mon; et. i; ss. *)
(*   - guclo simg_indC_spec. econs; eauto. *)
(*   - guclo simg_indC_spec. econs; eauto. i. specialize (SIM x). des. eapply IH; ss. *)
(*   - guclo simg_indC_spec. econs; eauto. des. esplits; eauto. *)
(*     + *)
(*     gstep. econs; eauto. gbase. eapply CIH in SIM. *)
(* Qed. *)

Variant invC (r: forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| invC_intro
    R0 R1 (RR: R0 -> R1 -> Prop) itr_src itr_tgt
    f0 f1
    f_src
    (TRUE: f_src = true)
    (SIM: r _ _ RR f0 f1 (tau;; itr_src) itr_tgt)
  :
    invC r RR f_src f1 itr_src itr_tgt
.

Hint Constructors invC: core.

Lemma invC_mon
      r1 r2
      (LE: r1 <7= r2)
  :
    invC r1 <7= invC r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve invC_mon: paco.
(* wrespectful7 *)
(* grespectful7 *)
Lemma invC_wrespectful: grespectful invC.
Proof.
  econs; eauto with paco.
  i.
  revert_until x2. gcofix CIH. i.
  inv PR. csc.
  dup SIM.
  apply LE in SIM. apply GF in SIM0.
  rename x12 into i0. rename x13 into i1.
  remember (tau;; i0) as tmp. revert i0 Heqtmp.
  induction SIM0 using _simg_ind2; intros ? EQ; irw in EQ; csc.
  - gfinal. right. pfold. eapply simg_mon; eauto. i. right. eapply CIH0. eapply rclo7_base; ss.
  - guclo simg_indC_spec. econs; eauto. eapply IHSIM0; ss.
Abort.

(* simg_bot_flag_up *)

(* Lemma simg_tau_inv_l_aux *)
(*         R *)
(*         i0 i1 *)
(*         (SIM: simg (@eq R) false false (tau;; i0) i1) *)
(*   : *)
(*   simg eq true true i0 i1 *)
(* . *)
(* Proof. *)
(*   ginit. revert_until R. gcofix CIH. i. *)
(*   remember (tau;; i0) as tmp. revert i0 Heqtmp. *)
(*   (* dependent induction SIM using simg_ind; intros ? EQ; irw in EQ; csc. *) *)
(*   induction SIM using simg_ind; intros ? EQ; irw in EQ; csc. *)
(*   - guclo flagC_spec. econs. *)
(*     3: { gfinal. right. eapply paco7_mon; et. i; ss. } *)
(*     { ss. } *)
(*     { ss. } *)
(*   - guclo simg_indC_spec. econs; eauto. *)
(*     eapply IHSIM; ss. i. eapply CIH. eapply simg_bot_flag_up; ss. *)
(*   - guclo simg_indC_spec. econs; eauto. i. specialize (SIM x). des. *)
(*     eapply IH; ss. i. eapply CIH. eapply simg_bot_flag_up; ss. *)
(*   - guclo simg_indC_spec. econs; eauto. des. esplits; eauto. *)
(*     eapply IH; ss. i. eapply CIH. eapply simg_bot_flag_up; ss. *)
(*   - admit "???". *)
(* Qed. *)

(* Lemma simg_tau_inv_l *)
(*         R *)
(*         f0 f1 i0 i1 *)
(*         (SIM: simg (@eq R) f0 f1 (tau;; i0) i1) *)
(*   : *)
(*   simg eq true f1 i0 i1 *)
(* . *)
(* (*** user can always instantiate f0 as true; it is easier to prove for user *)
(* Then we have: *)
(* ``` *)
(*         (SIM: simg (@eq R) true f1 (tau;; i0) i1) *)
(*   : *)
(*   simg eq true f1 i0 i1 *)
(* ``` *)
(* but for stronger CIH we put f0. *)
(*  ***) *)
(* Proof. *)
(*   ginit. revert_until R. gcofix CIH. i. *)
(*   remember (tau;; i0) as tmp. revert i0 Heqtmp. *)
(*   induction SIM using simg_ind; intros ? EQ; irw in EQ; csc. *)
(*   - gfinal. right. eapply paco7_mon; et. i; ss. *)
(*   - guclo simg_indC_spec. econs; eauto. *)
(*   - guclo simg_indC_spec. econs; eauto. i. specialize (SIM x). des. eapply IH; ss. *)
(*   - guclo simg_indC_spec. econs; eauto. des. esplits; eauto. *)
(*   - gfinal. right. eapply paco7_mon; try eapply simg_tau_inv_l_aux; et. i; ss. *)
(* Qed. *)








(* SIM1 : simg eq f2 f3 (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) itr2 *)

(*     remember (tau;; i0) as tmp. revert i0 Heqtmp. *)

(*     (* remember false as tmp2 in SIM at 2. revert Heqtmp2. *) *)
(*     remember false as tmp2 in SIM at 1. revert Heqtmp2. *)
(*     remember false as tmp3 in SIM at 1. revert Heqtmp3. *)
(*     (* induction SIM using simg_ind; intros ? ? EQ; irw in EQ; csc. *) *)

(*     (* punfold SIM. destruct SIM; intros ? EQ; irw in EQ; csc. *) *)
(*     (* eapply simg_ind. *) *)

(*     induction SIM using simg_ind. 9: { intros ??? EQ; irw in EQ; csc. *)
(*     (* induction SIM using simg_ind; intros ?? EQ; irw in EQ; csc. *) *)
(*     + eapply gpaco7_gupaco; eauto with paco. eapply flagC_spec. econs. *)
(*       3: { gfinal. right. eapply paco7_mon; et. i; ss. } *)
(*       { ss. } *)
(*       { ss. } *)
(*     + guclo simg_indC_spec. econs; eauto. *)
(*     + guclo simg_indC_spec. econs; eauto. i. specialize (SIM x). des. eapply IH; ss. *)
(*     + guclo simg_indC_spec. econs; eauto. des. esplits; eauto. *)
(*     + *)
(*       gstep. econs; eauto. gbase. gfinal. right. eapply paco7_mon; et. i; ss. *)
(*   - guclo simg_indC_spec. econs; eauto. *)
(*   - guclo simg_indC_spec. econs; eauto. i. specialize (SIM x). des. eapply IH; ss. *)
(*   - guclo simg_indC_spec. econs; eauto. des. esplits; eauto. *)
(*     + *)
(*     gstep. econs; eauto. gbase. eapply CIH in SIM. *)
(* Qed. *)

(*   CIH : forall (f0 f1 : bool) (i0 i1 : itree eventE R), simg eq f0 f1 (tau;; i0) i1 -> r R R eq true f1 i0 i1 *)
(*   f0, f1 : bool *)
(*   i0, i1 : itree eventE R *)
(*   SIM : simg eq f0 f1 (tau;; i0) i1 *)
(*   ============================ *)
(*   gpaco7 _simg (cpn7 _simg) bot7 r R R eq true f1 i0 i1 *)

(*   CIH : forall (f0 f1 : bool) (i0 i1 : itree eventE R), simg eq f0 f1 (tau;; i0) i1 -> r R R eq true f1 i0 i1 *)
(*   itr_tgt, i0 : itree eventE R *)
(*   SIM : simg eq false false (tau;; i0) itr_tgt *)
(*   ============================ *)
(*   gpaco7 _simg (cpn7 _simg) bot7 r R R eq true true i0 itr_tgt *)


Goal forall (P: nat -> Prop) n, le n 42 -> P n.
Proof.
  intros.
  induction H.
  2: {
Abort.
  (* H : n <= m *)
  (* IHle : P n *)
  (* ============================ *)
  (* P n *)

Goal forall (P: nat -> Prop) n, le n 42 -> P n.
Proof.
  intros.
  destruct H.
  2: {
Abort.
  (* H : n <= m *)
  (* ============================ *)
  (* P n *)

Goal forall (P: nat -> Prop) n, le n 42 -> P n.
Proof.
  intros.
  (* destruct H eqn:T. *)
  dependent destruction H.
  2: { subst.
Abort.
  (* H : n <= 41 *)
  (* ============================ *)
  (* P n *)

Goal forall (P: nat -> Prop) n, le n 42 -> P n.
Proof.
  intros.
  inv H.
  2: {
Abort.
  (* H1 : n <= 41 *)
  (* ============================ *)
  (* P n *)

Goal forall (P: nat -> Prop) n, le n 42 -> P n.
Proof.
  intros.
  remember 42 as tmp. revert Heqtmp.
  induction H.
  2: { i. subst.
Abort.

  (* H : n <= m *)
  (* IHle : m = 42 -> P n *)
  (* Heqtmp : S m = 42 *)
  (* ============================ *)
  (* P n *)

Goal Nat.even 42 -> Nat.even (42 + 2).
  i.
  induction H.
Abort.
  (* Nat.even x *)

Goal Nat.even 42 -> Nat.even (42 + 2).
  i.
  remember 42 as tmp. revert Heqtmp.
  induction H.
Abort.
  (* tmp = 42 -> Nat.even x *)



Lemma trans_aux
  R
  (itr0 itr1 itr2: itree eventE R)
  f0 f1 f2 f3
  (SIM0: simg eq f0 f1 itr0 itr1)
  (SIM1: simg eq f2 f3 itr1 itr2)
  :
  <<SIM: simg eq (f0) (f3) itr0 itr2>>
.
Proof.
  ginit.
  revert_until R.
  gcofix CIH.
  i.
  revert SIM1. revert itr2. revert f2 f3.
  induction SIM0 using simg_ind; i; clarify.
  - gfinal. right. eapply paco7_mon.
    { eapply simg_bot_flag_up; et. ginit. guclo flagC_spec. }
    i; ss.
    (* et. induction SIM1 using simg_ind; clarify. *)
    (* + gstep. econs; eauto. *)
    (* + gstep. econs; eauto. i. clarify. *)
    (*   eapply gpaco7_gupaco; eauto with paco. eapply flagC_spec. *)
    (*   econs. *)
    (*   3: { gbase. eapply CIH. *)
    (*        - eapply SIM; try refl. *)
    (*        - instantiate (1:=false). instantiate (1:=false). admit "refl". } *)
    (*   { ss. } *)
    (*   { ss. } *)
    (* + bsimpl. guclo simg_indC_spec. econs; eauto. guclo flagC_spec. *)
    (* + bsimpl. guclo simg_indC_spec. econs; eauto. *)
    (* + des. bsimpl. guclo simg_indC_spec. econs; eauto. esplits; eauto. guclo flagC_spec. *)
    (* + bsimpl. guclo simg_indC_spec. econs; eauto. i. exploit SIM; eauto. intro T; des. eauto. *)
    (* + bsimpl. guclo simg_indC_spec. econs; eauto. i. exploit SIM; eauto. intro T; des. eauto. guclo flagC_spec. *)
    (* + des. bsimpl. guclo simg_indC_spec. econs; eauto. *)
    (* + guclo flagC_spec. econs; revgoals. *)
    (*   { gfinal. right. eapply paco7_mon; eauto. i; ss. } *)
    (*   { ss. } *)
    (*   { ss. } *)
    (*   (* bsimpl. gstep. econs; eauto. gbase. change (false) with (false || false). eapply CIH; eauto. *) *)
    (*   (* admit "refl". *) *)
  - remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. revert Heqtmp.
    assert(T: simg eq true true tmp itr2).
    { ginit. guclo flagC_spec. }
    eapply simg_bot_flag_up in T. clear SIM1.
    (* instantiate (1:=false) in T. remember false as tmp1 in T. revert Heqtmp1. *)
    (* instantiate (1:=false) in T. remember false as tmp2 in T. revert Heqtmp2. *)
    (* induction T using simg_ind; intros ???EQ; irw in EQ; csc. *)
    instantiate (1:=f3) in T. instantiate (1:=f_src) in T.
    induction T using simg_ind; intros ?EQ; irw in EQ; csc.
    + change (fun x : Any.t => ktr_src1 x) with ktr_src1 in *.
      change (fun x : Any.t => ktr_tgt0 x) with ktr_tgt0 in *. subst.
      gstep. econs; eauto. i. subst. gbase. eapply CIH; et.
    + guclo simg_indC_spec. econs; eauto. eapply IHT. irw; ss.
    + guclo simg_indC_spec. econs; eauto. i. spc SIM0. des. eapply IH. irw; ss.
    + guclo simg_indC_spec. econs; eauto. des. esplits; et. eapply IH. irw; ss.
    + gstep. econs; eauto. gbase. eapply CIH; et.
      rewrite <- bind_trigger. ginit. gstep. econs; eauto. i. subst. gfinal. right. eapply paco7_mon; try eapply SIM; ss.
  - guclo simg_indC_spec. econs; eauto.
  - eapply IHSIM0. eapply simg_tau_inv_l; et.
  - des. guclo simg_indC_spec. econs; eauto.
  - remember (` x : _ <- trigger (Choose X);; ktr_tgt0 x) as tmp. revert Heqtmp.
    assert(T: simg eq true true tmp itr2).
    { ginit. guclo flagC_spec. }
    eapply simg_bot_flag_up in T. clear SIM1.
    instantiate (1:=f3) in T. instantiate (1:=f_src) in T.
    (* generalize dependent itr_src0. *)
    (* generalize dependent ktr_tgt0. clear_tac. *)
    induction T using simg_ind; intros ?EQ; irw in EQ; csc.
    + guclo simg_indC_spec. econs; et. eapply IHT; et. irw; ss.
    + assert(ktr_src0 = ktr_tgt0) by eauto. subst. clear_tac.
      des. eapply SIM; et.
    + guclo simg_indC_spec. econs; et. i. eapply SIM0; et. irw; ss.
    + des. guclo simg_indC_spec. econs; et. esplits; et. eapply IH; et. irw; ss.
    + gstep. econs; eauto. gbase. eapply CIH; et.
      ginit. guclo simg_indC_spec. rewrite <- bind_trigger. econs; et. i.
      spc SIM. des.
      eapply simg_bot_flag_up in SIM0. gfinal. right. eapply paco7_mon; eauto.
  - guclo simg_indC_spec. econs; eauto.
    i. spc SIM. des. eapply IH; et.
  - des. eapply IH; et. instantiate (1:=f2). clear IH. clear_tac. clear SIM0.
    eapply simg_tau_take_l; et.
  -
  (* CIH : forall (itr0 itr1 itr2 : itree eventE R) (f0 f1 f2 f3 : bool), *)
  (*       simg eq f0 f1 itr0 itr1 -> simg eq f2 f3 itr1 itr2 -> r R R eq f0 f3 itr0 itr2 *)
  (* itr_src, itr_tgt : itree eventE R *)
  (* SIM0 : simg eq false false itr_src itr_tgt *)
  (* f2, f3 : bool *)
  (* itr2 : itree eventE R *)
  (* SIM1 : simg eq f2 f3 itr_tgt itr2 *)
  (* ============================ *)
  (* gpaco7 _simg (cpn7 _simg) bot7 r R R eq true f3 itr_src itr2 *)
    revert SIM0. revert itr_src. induction SIM1 using simg_ind; i; clarify.
  (*   + remember (Ret r_tgt) as tmp. revert Heqtmp. *)
  (*     remember false as tmp1 in SIM0 at 1. clear Heqtmp1. *)
  (*     remember false as tmp2 in SIM0 at 1. clear Heqtmp2. *)
  (*     induction SIM0 using simg_ind; intros ?EQ; irw in EQ; csc. *)
  (*     * gstep. econs; eauto. *)
  (*     * guclo simg_indC_spec. econs; et. *)
  (*     * des. guclo simg_indC_spec. econs; et. *)
  (*     * guclo simg_indC_spec. econs; et. i. eapply SIM; ss. *)
  (*     *  *)
  (* (* SIM0 : simg eq false false itr_src (Ret r_tgt) *) *)
  (* (* ============================ *) *)
  (* (* gpaco7 _simg (cpn7 _simg) bot7 r R R eq true f_tgt itr_src (Ret r_tgt) *) *)
    + remember (Ret r_tgt) as tmp. revert Heqtmp.
      remember false as tmp1 in SIM0 at 1. revert Heqtmp1.
      remember false as tmp2 in SIM0 at 1. revert Heqtmp2.
      induction SIM0 using simg_ind; intros ???EQ; irw in EQ; csc.
      * gstep. econs; eauto.
      * guclo simg_indC_spec. econs; et. guclo flagC_spec. econs.
        3: { gfinal. right. eapply paco7_mon; et. i; ss. }
        { ss. }
        { ss. }
      * des. guclo simg_indC_spec. econs; et. esplits; et. guclo flagC_spec. econs.
        3: { gfinal. right. eapply paco7_mon; et. i; ss. }
        { ss. }
        { ss. }
      * des. guclo simg_indC_spec. econs; et. esplits; et. guclo flagC_spec. econs.
        3: { gfinal. right. eapply paco7_mon; try apply SIM. i; ss. }
        { ss. }
        { ss. }
    + remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_src0 x) as tmp. revert Heqtmp.
      assert(T: simg eq true true itr_src tmp).
      { ginit. guclo flagC_spec. }
      eapply simg_bot_flag_up in T. clear SIM0.
      (* instantiate (1:=false) in T. remember false as tmp1 in T. revert Heqtmp1. *)
      (* instantiate (1:=false) in T. remember false as tmp2 in T. revert Heqtmp2. *)
      (* induction T using simg_ind; intros ???EQ; irw in EQ; csc. *)
      instantiate (1:=f_tgt) in T. instantiate (1:=true) in T.
      remember true as tmp1 in T. clear Heqtmp1.
      induction T using simg_ind; intros ?EQ; irw in EQ; csc.
      * assert(ktr_tgt1 = ktr_src0) by eauto; subst.
        gstep. econs; eauto. i. subst. gbase. eapply CIH; et.
      * guclo simg_indC_spec. econs; eauto. eapply IHT. irw; ss.
      * guclo simg_indC_spec. des. econs; eauto. esplits; et. eapply IH. irw; ss.
      * guclo simg_indC_spec. econs; eauto. i. eapply SIM0. irw; ss.
      * gstep. econs; eauto. gbase. eapply CIH; et.
        rewrite <- bind_trigger. ginit. gstep. econs; eauto. i. subst. gfinal. right. eapply paco7_mon; try eapply SIM; ss.
    + eapply IHSIM1. eapply simg_tau_inv_r; et.
    + guclo simg_indC_spec. econs; eauto.
    + des. eapply IH; et. eapply simg_tau_choose_r; et.
    + guclo simg_indC_spec. econs; eauto.
      i. spc SIM. des. eapply IH; et.
    + remember (` x : _ <- trigger (Take X);; ktr_src0 x) as tmp. revert Heqtmp.
      assert(T: simg eq true true itr_src tmp).
      { ginit. guclo flagC_spec. }
      eapply simg_bot_flag_up in T. clear SIM0.
      instantiate (1:=f_tgt) in T. instantiate (1:=true) in T.
      remember true as tmp1 in T. clear Heqtmp1.
      (* generalize dependent itr_src0. *)
      (* generalize dependent ktr_tgt0. clear_tac. *)
      induction T using simg_ind; intros ?EQ; irw in EQ; csc.
      * guclo simg_indC_spec. econs; et. eapply IHT; et. irw; ss.
      * guclo simg_indC_spec. econs; et. des. esplits; et. eapply IH; et. irw; ss.
      * guclo simg_indC_spec. econs; et. i. eapply SIM0; et. irw; ss.
      * assert(ktr_src0 = ktr_tgt0) by eauto. subst. clear_tac.
        des. spc SIM. des. eapply IH0; et.
        eapply simg_bot_flag_up. ginit. guclo flagC_spec.
      * gstep. econs; eauto. gbase. eapply CIH; et.
        ginit. guclo simg_indC_spec. rewrite <- bind_trigger. econs; et. i.
        spc SIM. des. clear - SIM0. gfinal. right.
        eapply simg_bot_flag_up.
        ginit. guclo flagC_spec.
    + des. guclo simg_indC_spec. econs; et.
    + gstep. econs; eauto. gbase. eapply CIH; et.
Unshelve.
  all: ss.
Qed.


    + guclo simg_indC_spec. econs; et. eapply IHT; et. irw; ss.
    + assert(ktr_src0 = ktr_tgt0) by eauto. subst. clear_tac.
      des. eapply SIM; et.
    + guclo simg_indC_spec. econs; et. i. eapply SIM0; et. irw; ss.
    + des. guclo simg_indC_spec. econs; et. esplits; et. eapply IH; et. irw; ss.
    + gstep. econs; eauto. gbase. eapply CIH; et.
      ginit. guclo simg_indC_spec. rewrite <- bind_trigger. econs; et. i.
      spc SIM. des.
      eapply simg_bot_flag_up in SIM0. gfinal. right. eapply paco7_mon; eauto.
      * des. guclo simg_indC_spec. econs; et. esplits; et. eapply IH; et. irw; ss.

      * gstep. econs; eauto. gbase. eapply CIH; et.
        ginit. guclo simg_indC_spec. rewrite <- bind_trigger. econs; et. i.
        spc SIM. des.
      eapply simg_bot_flag_up in SIM0. gfinal. right. eapply paco7_mon; eauto.
    + guclo simg_indC_spec. econs; eauto.
      i. spc SIM. des. eapply IH; et.
    + des. eapply IH; et. instantiate (1:=f2). clear IH. clear_tac. clear SIM0.
      eapply simg_tau_take_l; et.
    + admit "".
    + admit "".
    + admit "".
    + admit "".
    + admit "".
    + admit "".
    + gstep. econs; eauto. gbase. eapply CIH; et.


      *
      dependent induction SIM0; try irw in x; csc.
    + gstep. econs; eauto. i. clarify.
      eapply gpaco7_gupaco; eauto with paco. eapply flagC_spec.
      econs.
      3: { gbase. eapply CIH.
           - eapply SIM; try refl.
           - instantiate (1:=false). instantiate (1:=false). admit "refl". }
      { ss. }
      { ss. }
    + bsimpl. guclo simg_indC_spec. econs; eauto. guclo flagC_spec.
    + bsimpl. guclo simg_indC_spec. econs; eauto.
    + des. bsimpl. guclo simg_indC_spec. econs; eauto. esplits; eauto. guclo flagC_spec.
    + bsimpl. guclo simg_indC_spec. econs; eauto. i. exploit SIM; eauto. intro T; des. eauto.
    + bsimpl. guclo simg_indC_spec. econs; eauto. i. exploit SIM; eauto. intro T; des. eauto. guclo flagC_spec.
    + des. bsimpl. guclo simg_indC_spec. econs; eauto.
    + guclo flagC_spec. econs; revgoals.
      { gfinal. right. eapply paco7_mon; eauto. i; ss. }
      { ss. }
      { ss. }

    destruct f3.
    + gstep. econs; eauto. gbase. eapply CIH; et. admit "".
    +
    guclo simg_indC_spec. econs; eauto.
  - remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. revert Heqtmp.
    induction SIM1 using simg_ind; intro EQ; irw in EQ; csc.
    + assert(ktr_src1 = ktr_tgt0).
      { extensionality x. eapply equal_f in H1. eauto. }
      gstep. econs; eauto. i. clarify. gbase. change true with (true || true). eapply CIH; eauto.
    + bsimpl. guclo simg_indC_spec. econs; eauto. eapply IHSIM1. rewrite <- bind_trigger; ss.
    + bsimpl. guclo simg_indC_spec. econs; eauto. i. eapply SIM0. rewrite <- bind_trigger; ss.
    + bsimpl. guclo simg_indC_spec. des. econs; eauto. esplits; eauto. eapply IH. rewrite <- bind_trigger; ss.
    + change (fun x : Any.t => ktr_tgt0 x) with ktr_tgt0 in SIM1.
      remember (vis (Syscall fn varg rvs) ktr_tgt0) as tmp. revert Heqtmp.
      (* punfold SIM1. induction SIM1 using _simg_ind2; intro EQ; irw in EQ; csc. <-- nothing changes *)
      (* remember false as tmp2 in SIM1. revert Heqtmp2. induction SIM1 using simg_ind; intros ? EQ; irw in EQ; csc. *)
      induction SIM1 using simg_ind; intros EQ; irw in EQ; csc.
      * gstep. econs; eauto. i. clarify. gbase. eapply CIH; eauto.
      * guclo simg_indC_spec. econs; eauto.
      * guclo simg_indC_spec. econs; eauto. i. eapply SIM0; ss.
      * des. guclo simg_indC_spec. econs; eauto.
      * rewrite <- bind_trigger in *.
        remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. revert Heqtmp.
        induction SIM1 using simg_ind; intro EQ; irw in EQ; csc.
        -- change (fun x : Any.t => ktr_src1 x) with ktr_src1 in H1.
           change (fun x : Any.t => ktr_tgt0 x) with ktr_tgt0 in H1. subst.
           gstep. econs; eauto. i. clarify. gbase. eapply CIH; eauto.
        -- guclo simg_indC_spec. econs; eauto. eapply IHSIM1. irw. ss.
        -- guclo simg_indC_spec. econs; eauto. i. eapply SIM0; ss. irw. ss.
        -- des. guclo simg_indC_spec. econs; eauto. esplits; eauto. eapply IH. irw. ss.
        -- replace f_src with true.
           gstep. econs; eauto.
           gbase. eapply CIH; eauto.
           ginit. rewrite <- bind_trigger. gstep. econs; eauto. i. subst. gfinal. right. eapply SIM; ss.
Abort.

Lemma trans_aux
  R
  (itr0 itr1 itr2: itree eventE R)
  f0 f3
  (SIM0: simg eq f0 false itr0 itr1)
  (SIM1: simg eq false f3 itr1 itr2)
  :
  <<SIM: simg eq (f0) (f3) itr0 itr2>>
.
Proof.
  ginit.
  revert_until R.
  gcofix CIH.
  i.
  revert SIM1. revert itr2. revert f3. remember false as tmp. revert Heqtmp.
  induction SIM0 using simg_ind; i; clarify.
  - admit "".
  - remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. revert Heqtmp.
    induction SIM1 using simg_ind; intro EQ; irw in EQ; csc.
    + assert(ktr_src1 = ktr_tgt0).
      { extensionality x. eapply equal_f in H1. eauto. }
      gstep. econs; eauto. i. clarify. gbase. eapply CIH; eauto. admit "ez". admit "ez".
    + bsimpl. guclo simg_indC_spec. econs; eauto. eapply IHSIM1. i. eapply CIH; et. rewrite <- bind_trigger; ss.
    + bsimpl. guclo simg_indC_spec. econs; eauto. i. eapply SIM0. i. eapply CIH; et. rewrite <- bind_trigger; ss.
    + bsimpl. guclo simg_indC_spec. des. econs; eauto. esplits; eauto. eapply IH. i. eapply CIH; et. rewrite <- bind_trigger; ss.
    + change (fun x : Any.t => ktr_tgt0 x) with ktr_tgt0 in SIM1.
      remember (vis (Syscall fn varg rvs) ktr_tgt0) as tmp. revert Heqtmp.
      (* punfold SIM1. induction SIM1 using _simg_ind2; intro EQ; irw in EQ; csc. <-- nothing changes *)
      induction SIM1 using simg_ind; intro EQ; irw in EQ; csc.
      * gstep. econs; eauto. i. clarify. gbase. eapply CIH; eauto.
      * guclo simg_indC_spec. econs; eauto.
      * guclo simg_indC_spec. econs; eauto. i. eapply SIM0; ss.
      * des. guclo simg_indC_spec. econs; eauto.
      * rewrite <- bind_trigger in *.
        remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. revert Heqtmp.
        induction SIM1 using simg_ind; intro EQ; irw in EQ; csc.
        -- change (fun x : Any.t => ktr_src1 x) with ktr_src1 in H1.
           change (fun x : Any.t => ktr_tgt0 x) with ktr_tgt0 in H1. subst.
           gstep. econs; eauto. i. clarify. gbase. eapply CIH; eauto.
        -- guclo simg_indC_spec. econs; eauto. eapply IHSIM1. irw. ss.
        -- guclo simg_indC_spec. econs; eauto. i. eapply SIM0; ss. irw. ss.
        -- des. guclo simg_indC_spec. econs; eauto. esplits; eauto. eapply IH. irw. ss.
        -- replace f_src with true.
           gstep. econs; eauto.
           gbase. eapply CIH; eauto.
           ginit. rewrite <- bind_trigger. gstep. econs; eauto. i. subst. gfinal. right. eapply SIM; ss.
Abort.

  R : Type
  r : forall x x0 : Type, (x -> x0 -> Prop) -> bool -> bool -> itree eventE x -> itree eventE x0 -> Prop
  CIH : forall (itr0 itr1 itr2 : itree eventE R) (f0 f1 f2 f3 : bool),
        simg eq f0 f1 itr0 itr1 -> simg eq f2 f3 itr1 itr2 -> r R R eq f0 f3 itr0 itr2
  f_src, f_tgt : bool
  ktr_src0, ktr_tgt0 : Any.t -> itree eventE R
  fn : string
  varg : Any.t
  rvs : Any.t -> Prop
  SIM : forall x_src x_tgt : Any.t, x_src = x_tgt -> simg eq true true (ktr_src0 x_src) (ktr_tgt0 x_tgt)
  itr_tgt : itree eventE R
  SIM1 : simg eq false false (vis (Syscall fn varg rvs) ktr_tgt0) itr_tgt
  ============================
  gpaco7 _simg (cpn7 _simg) bot7 r R R eq f_src true (` x : _ <- trigger (Syscall fn varg rvs);; ktr_src0 x) itr_tgt


        des. guclo simg_indC_spec. econs; eauto. esplits; eauto.
        pclearbot. change true with (true || true). eapply CIH; eauto.
        bsimpl. gstep. econs; eauto. gbase. change (false) with (false || false). eapply CIH; eauto.
        rewrite <- bind_trigger; ss.
        pfold. econs; eauto. i. subst. left. eapply SIM; ss.

      rewrite <- bind_trigger in *; ss.
      bsimpl. gstep. econs; eauto. gbase. change (false) with (false || false). eapply CIH; eauto.
      rewrite <- bind_trigger; ss.
      pfold. econs; eauto. i. subst. left. eapply SIM; ss.
  - bsimpl. guclo simg_indC_spec. econs; eauto. eapply IHSIM0; eauto.
  - bsimpl.
    destruct f3 eqn:T; subst.
    2: { bsimpl.
    (* destruct (f_tgt || f3) eqn:T. *)
    + bsimpl. eapply IHSIM0.
      { admit "maybe?". }
    + bsimpl. des; subst.
      guclo euttC_spec.
Abort.

Lemma trans_aux
  R
  (itr0 itr1 itr2: itree eventE R)
  f0 f1 f2 f3
  (SIM0: simg eq f0 f1 itr0 itr1)
  (SIM1: simg eq f2 f3 itr1 itr2)
  :
  <<SIM: simg eq (f0 || f2) (f1 || f3) itr0 itr2>>
.
Proof.
  ginit.
  revert_until R.
  gcofix CIH.
  i.
  revert SIM1. revert itr2. revert f2 f3.
  induction SIM0 using simg_ind; i; clarify.
  - induction SIM1 using simg_ind; clarify.
    + gstep. econs; eauto.
    + gstep. econs; eauto. i. clarify.
      eapply gpaco7_gupaco; eauto with paco. eapply flagC_spec.
      econs.
      3: { gbase. eapply CIH.
           - eapply SIM; try refl.
           - instantiate (1:=false). instantiate (1:=false). admit "refl". }
      { ss. }
      { ss. }
    + bsimpl. guclo simg_indC_spec. econs; eauto.
    + bsimpl. guclo simg_indC_spec. econs; eauto.
    + des. bsimpl. guclo simg_indC_spec. econs; eauto.
    + bsimpl. guclo simg_indC_spec. econs; eauto. i. exploit SIM; eauto. intro T; des. eauto.
    + bsimpl. guclo simg_indC_spec. econs; eauto. i. exploit SIM; eauto. intro T; des. eauto.
    + des. bsimpl. guclo simg_indC_spec. econs; eauto.
    + bsimpl. gstep. econs; eauto. gbase. change (false) with (false || false). eapply CIH; eauto.
      admit "refl".
  - remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. revert Heqtmp.
    induction SIM1 using simg_ind; intro EQ; irw in EQ; csc.
    + assert(ktr_src1 = ktr_tgt0).
      { extensionality x. eapply equal_f in H1. eauto. }
      gstep. econs; eauto. i. clarify. gbase. change true with (true || true). eapply CIH; eauto.
    + bsimpl. guclo simg_indC_spec. econs; eauto. eapply IHSIM1. rewrite <- bind_trigger; ss.
    + bsimpl. guclo simg_indC_spec. econs; eauto. i. eapply SIM0. rewrite <- bind_trigger; ss.
    + bsimpl. guclo simg_indC_spec. des. econs; eauto. esplits; eauto. eapply IH. rewrite <- bind_trigger; ss.
    + bsimpl. gstep. econs; eauto. gbase. change (false) with (false || false). eapply CIH; eauto.
      rewrite <- bind_trigger; ss.
      pfold. econs; eauto. i. subst. left. eapply SIM; ss.
  - bsimpl. guclo simg_indC_spec. econs; eauto. eapply IHSIM0; eauto.
  - bsimpl.
    destruct f3 eqn:T; subst.
    2: { bsimpl.
    (* destruct (f_tgt || f3) eqn:T. *)
    + bsimpl. eapply IHSIM0.
      { admit "maybe?". }
    + bsimpl. des; subst.
      guclo euttC_spec.

  SIM0 : simg eq f_src true itr_src0 itr_tgt0
  SIM1 : simg eq f2 f3 (tau;; itr_tgt0) itr2
  ---------------> simg eq (f2-1) f3 itr_tgt0 itr2
  IHSIM0 : simg eq f2 f3 itr_tgt0 itr2 -> gpaco7 _simg (cpn7 _simg) bot7 r R R eq (f_src+f2) (1+f3) itr_src0 itr2
  ---------------> simg eq (f2-1) f3 itr_tgt0 itr2 -> gpaco7 _simg (cpn7 _simg) bot7 r R R eq (f_src+f2-1) (1+f3) itr_src0 itr2
  ============================
  gpaco7 _simg (cpn7 _simg) bot7 r R R eq (f_src+f2) (f_tgt+f3) itr_src0 itr2

    TTTTTTTTTTTTTTTTTT
  itr0, itr1, itr2 : itree eventE R
  f0, f1, f2, f3 : bool
  SIM0 : simg eq f0 f1 itr0 itr1
  SIM1 : simg eq f2 f3 itr1 itr2
  ============================
  gpaco7 _simg (cpn7 _simg) bot7 r R R eq (f0 || f2) (f1 || f3) itr0 itr2
    assert(LEMMA: simg eq true f3 (itr_tgt0) itr2).
    { admit "??". }

    guclo simg_indC_spec. econs; eauto.
    TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT
    remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. revert Heqtmp.
    induction SIM1 using simg_ind; intro EQ; irw in EQ; csc.
    + assert(ktr_src1 = ktr_tgt0).
      { extensionality x. eapply equal_f in H1. eauto. }
      gstep. econs; eauto. i. clarify. gbase. change true with (true || true). eapply CIH; eauto.
    + bsimpl. guclo simg_indC_spec. econs; eauto. eapply IHSIM1. rewrite <- bind_trigger; ss.
    + bsimpl. guclo simg_indC_spec. econs; eauto. i. eapply SIM0. rewrite <- bind_trigger; ss.
    + bsimpl. guclo simg_indC_spec. des. econs; eauto. esplits; eauto. eapply IH. rewrite <- bind_trigger; ss.
    + bsimpl. gstep. econs; eauto. gbase. change (false) with (false || false). eapply CIH; eauto.
      rewrite <- bind_trigger; ss.
      pfold. econs; eauto. i. subst. left. eapply SIM; ss.
  -

  SIM : forall x_src x_tgt : Any.t, x_src = x_tgt -> simg eq true true (ktr_src0 x_src) (ktr_tgt0 x_tgt)
  x_tgt : Any.t
  ============================
  simg eq f_tgt f_tgt (ktr_src0 x_tgt) ?itr1

goal 2 (ID 2499) is:
 simg eq f_tgt f_tgt ?itr1 (ktr_tgt0 x_tgt)
Qed.

Lemma trans
  R
  (itr0 itr1 itr2: itree eventE R)
  (SIM0: simg eq false false itr0 itr1)
  (SIM1: simg eq false false itr1 itr2)
  :
  <<SIM: simg eq false false itr0 itr2>>
.
Proof.
  ginit.
  revert_until R.
  gcofix CIH.
  i.
  induction SIM0 using simg_ind; clarify.
  - induction SIM1 using simg_ind; clarify.
    + gstep. econs; eauto.
    + gstep. econs; eauto. i. clarify. gbase. 
      eapply CIH. eauto with paco.  guclo simg_indC_spec. econs; eauto. i. gbase.
  punfold SIM0. punfold SIM1.
  induction SIM0 using simg_ind2.
  intros. eapply grespect_uclo; eauto with paco. eapply euttC_grespectful.
Qed.

Context {CONFS CONFT: EMSConfig}.
Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

Theorem adequacy_global_itree itr_src itr_tgt
        (SIM: simg eq false false itr_src itr_tgt)
  :
    Beh.of_program (@ModSemL.compile_itree CONFT itr_tgt)
    <1=
    Beh.of_program (@ModSemL.compile_itree CONFS itr_src).
Proof.
  unfold Beh.of_program. ss.
  remember false as o_src0 in SIM at 1.
  remember false as o_tgt0 in SIM at 1. clear Heqo_src0 Heqo_tgt0.
  i. eapply adequacy_aux; et.
  instantiate (1:=o_tgt0). instantiate (1:=o_src0). clear x0 PR.
  generalize itr_tgt at 1 as md_tgt.
  generalize itr_src at 1 as md_src. i. ginit.
  revert o_src0 o_tgt0 itr_src itr_tgt SIM. gcofix CIH.
  i. induction SIM using simg_ind; i; clarify.
  { gstep. destruct (finalize r_tgt) eqn:T.
    { eapply sim_fin; ss; cbn; des_ifs; rewrite FINSAME in *; clarify. }
    { eapply sim_angelic_src.
      { cbn. des_ifs; rewrite FINSAME in *; clarify. }
      i. exfalso. inv STEP.
    }
  }
  { gstep. eapply sim_vis; ss. i.
    eapply step_trigger_syscall_iff in STEP. des. clarify.
    esplits.
    { eapply step_trigger_syscall; et. }
    { gbase. eapply CIH. hexploit SIM; et. }
  }
  { guclo sim_indC_spec. eapply sim_indC_demonic_src; ss.
    esplits; eauto. eapply step_tau; et.
  }
  { guclo sim_indC_spec. eapply sim_indC_demonic_tgt; ss. i.
    eapply step_tau_iff in STEP. des. clarify.
  }
  { des. guclo sim_indC_spec. eapply sim_indC_demonic_src; ss.
    esplits; eauto. eapply step_trigger_choose; et.
  }
  { guclo sim_indC_spec. eapply sim_indC_demonic_tgt; ss.
    i.  eapply step_trigger_choose_iff in STEP. des. clarify.
    hexploit (SIM x); et. i. des. esplits; eauto.
  }
  { guclo sim_indC_spec. eapply sim_indC_angelic_src; ss. i.
    eapply step_trigger_take_iff in STEP. des. clarify.
    hexploit (SIM x); et. i. des. esplits; et.
  }
  { des. guclo sim_indC_spec. eapply sim_indC_angelic_tgt; ss.
    esplits; eauto. eapply step_trigger_take; et.
  }
  { gstep. eapply sim_progress; eauto. gbase. auto. }
Qed.


Variable md_src md_tgt: ModL.t.
Let ms_src: ModSemL.t := md_src.(ModL.enclose).
Let ms_tgt: ModSemL.t := md_tgt.(ModL.enclose).

Section ADEQUACY.
Hypothesis (SIM: simg eq false false (@ModSemL.initial_itr ms_src CONFS (Some (ModL.wf md_src))) (@ModSemL.initial_itr ms_tgt CONFT (Some (ModL.wf md_tgt)))).


Theorem adequacy_global: Beh.of_program (@ModL.compile _ CONFT md_tgt) <1= Beh.of_program (@ModL.compile _ CONFS md_src).
Proof.
  eapply adequacy_global_itree. eapply SIM.
Qed.
End ADEQUACY.
End SIM.

Hint Constructors _simg.
Hint Unfold simg.
Hint Resolve simg_mon: paco.
Hint Constructors flagC: core.
Hint Resolve flagC_mon: paco.
Hint Constructors bindR: core.
Hint Unfold bindC: core.
Hint Constructors simg_indC: core.
Hint Resolve sim_indC_mon: paco.


Variant _simg_safe
          (simg: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (f_src f_tgt: bool): (itree eventE R0) -> (itree eventE R1) -> Prop :=
| simg_safe_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg_safe simg RR f_src f_tgt (Ret r_src) (Ret r_tgt)
| simg_safe_syscall
    ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR true true (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg_safe simg RR f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)

| simg_safe_tauL
    itr_src0 itr_tgt0
    (TAUL: True)
    (SIM: simg _ _ RR true f_tgt itr_src0 itr_tgt0)
  :
    _simg_safe simg RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
| simg_safe_tauR
    itr_src0 itr_tgt0
    (TAUR: True)
    (SIM: simg _ _ RR f_src true itr_src0 itr_tgt0)
  :
    _simg_safe simg RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

| simg_safe_chooseR
    X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (SIM: forall x, simg _ _ RR f_src true itr_src0 (ktr_tgt0 x))
  :
    _simg_safe simg RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

| simg_safe_takeL
    X ktr_src0 itr_tgt0
    (TAKEL: True)
    (SIM: forall x, simg _ _ RR true f_tgt (ktr_src0 x) itr_tgt0)
  :
    _simg_safe simg RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)
.

Lemma simg_safe_spec:
  _simg_safe <8= gupaco7 _simg (cpn7 _simg).
Proof.
  i. eapply simg_indC_spec. inv PR.
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
Qed.










