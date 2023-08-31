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



Section ALGEBRA.

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

Theorem GSimMod
  md0 md1
  (SIMSK: md0.(Mod.sk) ≡ md1.(Mod.sk))
  (SEM: forall sk, md0.(Mod.get_modsem) sk ⊑B md1.(Mod.get_modsem) sk)
  :
  md0 ⊑B md1
.
Proof.
  destruct (classic (Sk.wf (Mod.sk md1))).
  2: { ii. eapply Mod.compile_not_wf in PR; ss.
       - subst. eapply Beh.nb_bottom.
       - intro T. r in T. des. rewrite SIMSK in T. ss.
  }
  assert(T: Sk.wf (Mod.sk md1) = Sk.wf (Mod.sk md0)).
  { eapply prop_ext. split; eapply Sk.wf_equiv; et. }
  { ii. des. do 2 r in SEM. unfold Mod.enclose in *. unfold ModSem.compile' in *.
    rename x0 into tr.
    specialize (SEM md0.(Mod.sk) H0 tr).
    unfold Mod.compile in *. unfold Mod.enclose in *. unfold Mod.wf in *.
    rewrite T.
    des_ifs_safe. erewrite Mod.get_modsem_Proper; et.
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
  { ss. rewrite SIMSK; ss. }
  i. cbn. do 2 r in SEM. et.
Qed.

Global Program Instance Mod_OPlusFactsWeak: OPlusFactsWeak (T:=Mod.t).
Next Obligation.
  i; cbn.
  eapply LSimMod; et.
  { ss. rewrite Sk.add_comm; ss. }
  i. ss. eapply oplus_comm_weak.
Qed.
Next Obligation.
  i; cbn.
  eapply LSimMod; et.
  { ss. rewrite Sk.add_assoc; ss. }
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
  i; cbn.
  eapply GSimMod.
  { ss. eapply Sk.add_comm; et. }
  i. ss. rewrite oplus_comm_weak. refl.
Qed.
Next Obligation.
  i; cbn.
  eapply GSimMod.
  { ss. rewrite Sk.add_assoc; et. }
  i. ss. rewrite oplus_assoc_weak. refl.
Qed.

Global Program Instance ModSem_EpsFacts: EpsFacts.
Next Obligation.
  i; cbn.
  rr. ss. rewrite Sk.add_unit_r. esplits; try refl. ii. upt. des_ifs.
Qed.
Next Obligation.
  i; cbn.
  rr. ss. rewrite Sk.add_unit_l. esplits; try refl. ii. upt. des_ifs.
Qed.

Global Program Instance refb_equiv: subrelation ((≡)) ((⊑B)).
Next Obligation.
  i; cbn.
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
  i; cbn.
  {
    do 2 r in H. specialize (H ε).
    rewrite <- eps_l. etrans; et.
    rewrite eps_l. refl.
  }
Qed.

Global Program Instance ModSem_RefBFacts: RefBFacts.

Global Program Instance ModSem_Ref_PreOrder: PreOrder ((⊑@{Mod.t})).
Next Obligation.
  ii; ss.
Qed.
Next Obligation.
  ii. eapply H0. eapply H; ss.
Qed.

Global Program Instance Mod_RefFacts: RefFacts (T:=Mod.t).
Next Obligation.
  do 3 r. i.
  unfold sqsubseteq, Mod.ref in *.
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
  - i. eapply equiv_ref_both.
    rr. ss. esplits; try refl. i. rewrite bar_idemp. refl.
  - i. eapply equiv_ref_both.
    rr. ss. esplits; try refl.
    { rewrite Sk.add_unit_r; refl. }
    i. rewrite bar_oplus. refl.
  - ii. rr in H. des. rr. esplits; ss; try refl. ii. rewrite H0; ss.
  - rr. ss.
Qed.
Next Obligation.
  ii. des. ss.
  destruct (classic (Sk.wf (Mod.sk ctx ⊕ Mod.sk a))).
  2: {
    eapply Mod.compile_not_wf in PR; ss. subst. eapply Beh.nb_bottom.
  }
  unfold Mod.compile in *. des_ifs.
  2: { ss. unfold Mod.wf in *. ss. contradict n. rewrite Sk.add_unit_r. eapply Sk.wf_mon; et. r. esplits; refl.
  }
  assert(T:=MRA.affinity). ss. do 4 r in T. ss.
  eapply T in PR. clear T.
  assert(U: (Mod.get_modsem ctx (Mod.sk ctx ⊕ Mod.sk a) ⊕ ε) ⊑B (Mod.get_modsem ctx (Mod.sk ctx ⊕ Sk.unit) ⊕ ε)).
  { rewrite ! eps_r.
    rewrite Mod.get_modsem_affine; et; try refl.
    { rewrite Sk.add_unit_r. rr. esplits; refl. }
  }
  eapply U.
  ss.
Qed.
Next Obligation.
  i; cbn.
  eapply LSimMod; ss.
  { rewrite Sk.add_unit_r. refl. }
  i. eapply (@MRA.bar_intro ModSem_MRA).
Qed.

End ALGEBRA.
