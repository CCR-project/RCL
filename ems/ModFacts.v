Require Import Coqlib Algebra.
Require Export sflib.
Require Export ITreelib.
Require Export ModSemE.
Require Export AList.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Permutation.
Require Import ModSem.
Require Import Mod ModSemFacts.

Set Implicit Arguments.



Section FACTS.

Context `{SK: Sk.ld}.

(* Global Program Instance enclose_equiv_Proper: Proper ((≡) ==> (eq)) (Mod.enclose). *)
(* Next Obligation. *)
(*   ii. rr in H0. des. unfold Mod.enclose. erewrite Mod.get_modsem_Proper; et. *)
(* Qed. *)

(* Global Program Instance enclose_equiv_Proper: Proper ((⊑B) ==> (⊑B)) (Mod.enclose). *)
(* Next Obligation. *)
(*   ii. rr in H0. do 2 spc H0. *)
(*   unfold Mod.compile in *. unfold ModSem.compile' in *. des_ifs; et. *)
(* Qed. *)

(* Global Program Definition ModSem_Mod (ms: ModSem.t): Mod.t := Mod.mk (fun _ => ms) (Sk.unit) _ _ _. *)
(* Next Obligation. refl. Qed. *)
(* Next Obligation. refl. Qed. *)

(* Global Program Instance enclose_equiv_Proper: Proper ((⊑) ==> (⊑)) (Mod.enclose). *)
(* Next Obligation. *)
(*   ii. rr in H. ss. specialize (H (ModSem_Mod ctx)). do 2 spc H. *)
(*   unfold Mod.compile in *. unfold ModSem.compile' in *. des_ifs; et. *)
(* Qed. *)

Lemma compile_not_wf
        `{EMSConfig}
        md tr
        (WF: ~ Mod.wf md)
        (TR: Beh.of_program (Mod.compile md) tr)
  :
  tr = Tr.nb
.
Proof.
  unfold Mod.compile in *. des_ifs; ss.
  - eapply ModSem.compile_not_wf; et.
  - punfold TR. inv TR; ss; csc.
    + punfold SPIN. inv SPIN; ss; csc. des; subst. ss.
    + rr in STEP. des; ss.
Qed.

Lemma ModSem_Mod_compile `{EMSConfig} md: ModSem.compile' (Mod.enclose md) (Mod.wf md) = Mod.compile md.
Proof. ss. Qed.

Theorem GSimMod
  md0 md1
  (SIMSK: md0.(Mod.sk) ≡ md1.(Mod.sk))
  (SEM: forall sk, md0.(Mod.get_modsem) sk ⊑B md1.(Mod.get_modsem) sk)
  :
  md0 ⊑B md1
.
Proof.
  destruct (classic (Sk.wf (Mod.sk md1))).
  2: { ii. eapply compile_not_wf in PR; ss.
       - subst. eapply Beh.nb_bottom.
       - intro T. r in T. des. rewrite SIMSK in T. ss.
  }
  assert(T: Sk.wf (Mod.sk md1) = Sk.wf (Mod.sk md0)).
  { eapply prop_ext. split; eapply Sk.wf_equiv; et. sym; et. }
  { ii. des. do 2 r in SEM. unfold Mod.enclose in *. unfold ModSem.compile' in *.
    rename x0 into tr.
    specialize (SEM md0.(Mod.sk) H0 (Mod.wf md0) tr).
    unfold Mod.compile in *. unfold Mod.enclose in *. unfold Mod.wf in *.
    rewrite T. erewrite Mod.get_modsem_Proper; et.
    { sym; et. }
  }
Qed.

Theorem LSimMod
  md0 md1
  (SIMSK: md0.(Mod.sk) ≡ md1.(Mod.sk))
  (SEM: forall sk, md0.(Mod.get_modsem) sk ⊑ md1.(Mod.get_modsem) sk)
  :
  md0 ⊑ md1
.
Proof.
  do 2 r. i.
  eapply GSimMod; et.
  { ss. rewrite SIMSK; ss. refl. }
  i. cbn. do 2 r in SEM. et.
Qed.

Global Program Instance Mod_OPlusFactsWeak: OPlusFactsWeak (T:=Mod.t).
Next Obligation.
  eapply LSimMod; et.
  { ss. rewrite Sk.add_comm; ss. refl. }
  i. ss. eapply oplus_comm_weak.
Qed.
Next Obligation.
  eapply LSimMod; et.
  { ss. rewrite Sk.add_assoc; ss. refl. }
  i. ss. eapply oplus_assoc_weak.
Qed.
Next Obligation.
  ii. rr in H. rr in H0. des; subst.
  rr. ss. esplits; et.
  - rewrite H. rewrite H0. refl.
  - ii. rewrite H1. rewrite H2. refl.
Qed.

Global Program Instance Mod_OPlusFactsWeak2: OPlusFactsWeak (T:=Mod.t) (H1:=Mod.refb).
Next Obligation.
  eapply GSimMod.
  { ss. eapply Sk.add_comm; et. }
  i. ss. rewrite oplus_comm_weak. refl.
Qed.
Next Obligation.
  eapply GSimMod.
  { ss. rewrite Sk.add_assoc; et. refl. }
  i. ss. rewrite oplus_assoc_weak. refl.
Qed.

Global Program Instance ModSem_EpsFacts: EpsFacts.
Next Obligation.
  rr. ss. rewrite Sk.add_unit_r. esplits; try refl. ii. upt. des_ifs.
Qed.
Next Obligation.
  rr. ss. rewrite Sk.add_unit_l. esplits; try refl. ii. upt. des_ifs.
Qed.
Next Obligation.
  rr. ss. esplits; try refl.
Qed.

Global Program Instance refb_equiv: subrelation ((≡)) ((⊑B)).
Next Obligation.
  rr in H. des; ss.
  eapply GSimMod; et. i.
  eapply refb_equiv.
  rewrite H0. refl.
Qed.

Global Program Instance refb_preorder: PreOrder ((⊑B)).
Next Obligation. ii; ss. Qed.
Next Obligation. ii. eapply H0. eapply H; ss. Qed.

Global Program Instance Mod_ref_refb: subrelation (⊑) ((⊑B)).
Next Obligation.
  {
    do 2 r in H. specialize (H ε).
    rewrite <- eps_l. etrans; et.
    rewrite eps_l. refl.
  }
Qed.

Global Program Instance ModSem_RefBFacts: RefBFacts.

Global Program Instance ModSem_Ref_PreOrder: PreOrder ((⊑)).
Next Obligation.
  ii; ss.
Qed.
Next Obligation.
  ii. eapply H0. eapply H; ss.
Qed.

Global Program Instance Mod_RefFacts: RefFacts (T:=Mod.t).
Next Obligation.
  do 3 r. i.
  unfold ref, Mod.ref in *.
  i. rewrite oplus_assoc_weak. rewrite H0.
  rewrite oplus_comm_weak. rewrite oplus_assoc_weak. rewrite H.
  rewrite oplus_assoc_weak2. rewrite oplus_comm_weak.
  rewrite oplus_assoc_weak2. refl.
Qed.
Next Obligation.
  r. i. rr in H; des.
  eapply LSimMod; et. i.
  eapply ref_equiv.
  rewrite H0. refl.
Qed.

Global Program Instance Mod_MRA: MRA.t := {
  car := Mod.t;
}.
Next Obligation.
  econs.
  - i. cut ( | |a| | ≡ |a| ).
    { intro T. rewrite T. refl. }
    rr. ss. esplits; try refl. i. set (Mod.get_modsem a sk0) as tmp.
    admit "Make equiv".
  - admit "Make equiv".
  - ii. rr in H. des. rr. esplits; ss; try refl. ii. rewrite H0; ss.
Qed.
Next Obligation.
  ii. des. ss.
  destruct (classic (Sk.wf (Mod.sk ctx ⊕ Mod.sk a))).
  2: {
    eapply compile_not_wf in PR; ss. subst. eapply Beh.nb_bottom.
  }
  assert(T:=MRA.affinity). ss. do 4 r in T. ss.
  rewrite <- ModSem_Mod_compile in PR. ss. eapply T in PR. clear T.
  rewrite <- ModSem_Mod_compile. ss.
  assert(U: (Mod.get_modsem ctx (Mod.sk ctx ⊕ Mod.sk a) ⊕ ε) ⊑B (Mod.get_modsem ctx (Mod.sk ctx ⊕ Sk.unit) ⊕ ε)).
  { rewrite ! eps_r.
    rewrite Mod.get_modsem_affine; et; try refl.
    { rewrite Sk.add_unit_r. rr. esplits; refl. }
  }
  eapply U.
  replace (Mod.wf (ctx ⊕ ε)) with (Mod.wf (ctx ⊕ a)) by admit "Remove P".
  ss.
Qed.
Next Obligation.
  eapply LSimMod; ss.
  { rewrite Sk.add_unit_r. refl. }
  i. eapply (@MRA.bar_intro ModSem_MRA).
Qed.

End FACTS.
