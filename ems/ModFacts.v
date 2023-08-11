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

Theorem GSimMod
  md0 md1
  (SIMSK: md0.(Mod.sk) ≡ md1.(Mod.sk))
  (SEM: forall sk, md0.(Mod.get_modsem) sk ⊑B md1.(Mod.get_modsem) sk)
  :
  md0 ⊑B md1
.
Proof.
  assert(T: Sk.wf (Mod.sk md1) = Sk.wf (Mod.sk md0)).
  { eapply prop_ext. split; eapply Sk.wf_equiv; et. sym; et. }
  destruct (classic (Sk.wf md0.(Mod.sk))).
  { ii. do 2 r in SEM. unfold Mod.enclose in *. unfold ModSem.compile' in *.
    specialize (SEM md0.(Mod.sk) H0 (Mod.wf md0) x0).
    unfold Mod.compile in *. unfold Mod.enclose in *. unfold Mod.wf in *.
    rewrite T. erewrite Mod.get_modsem_Proper; et.
    { sym; et. }
    { rewrite T; et. }
  }
  {
    ii. unfold Mod.compile, Mod.enclose in *. des_ifs.
    - punfold PR. inv PR; csc; ss.
      { punfold SPIN; inv SPIN; ss. des; ss. unfold ModSem.initial_itr, guarantee in *. irw in STEP0. inv STEP0; ss; csc. }
      { eapply Beh.nb_bottom. }
      { rr in STEP. des; subst. ss. unfold ModSem.initial_itr, guarantee in *. irw in STEP0. inv STEP0; ss; csc. }
    - specialize (SEM md0.(Mod.sk) H0 (Mod.wf md0) x0). rewrite Heq0 in *. ss.
      spc SEM. unfold ModSem.compile' in *. rewrite Heq in *.
      unfold Mod.compile in *. unfold Mod.enclose in *. unfold Mod.wf in *.
      rewrite T. erewrite Mod.get_modsem_Proper; et.
      { sym; et. }
      { rewrite T; et. }
      specialize (SEM admit "".
    - rr. pfold. econsr; et. rr. ii; ss.
      cut (x0 = Tr.nb).
      { i. subst. eapply Beh.nb_bottom. }
      clear - PR.
      punfold PR. induction PR using Beh.of_state_ind; csc; ss.
      { admit "". }
      { rr in STEP. ss.
      { clear - SPIN. exfalso.
        punfold SPIN. induction SPIN; ii; ss.
        punfold SPIN; inv SPIN; ss. des; ss. unfold ModSem.initial_itr, guarantee in *. irw in STEP0. inv STEP0; ss; csc. }
      { eapply Beh.nb_bottom. }
      { rr in STEP. des; subst. ss. unfold ModSem.initial_itr, guarantee in *. irw in STEP0. inv STEP0; ss; csc. }
    -
    -
    
    ii. unfold Mod.compile in *. des_ifs.
    { do 2 r in SEM. unfold Mod.enclose in *. unfold ModSem.compile' in *.
      specialize (SEM md0.(Mod.sk) H0 (Mod.wf md0) x0). rewrite Heq0 in *.
      erewrite Mod.get_modsem_Proper in Heq; et.
      2: { sym; eauto. }
      2: { rewrite T; et. }
      rewrite Heq in *. unfold Mod.wf in *. rewrite T. et.
    }
    { admit "". }
    { do 2 r in SEM. unfold Mod.enclose in *. unfold ModSem.compile' in *.
      specialize (SEM md0.(Mod.sk) H0 (Mod.wf md0) x0). rewrite Heq0 in *.
      erewrite Mod.get_modsem_Proper in Heq; et.
      2: { sym; eauto. }
      2: { rewrite T; et. }
      rewrite Heq in *. unfold Mod.wf in *. et.
    }
    { admit "". }
  }
  { ii. unfold Mod.compile in PR.
    admit "".
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

Global Program Instance ModSem_ref_refB: subrelation (⊑) ((⊑B)).
Next Obligation.
  do 1 r. i. do 2 r in H. specialize H with mytt. upt. des_ifs.
Qed.

Global Program Instance ModSem_RefBFacts: RefBFacts.
Next Obligation.
  econs.
  - ii; ss.
  - ii. eapply H0. eapply H; ss.
Qed.
Next Obligation.
  etrans; typeclasses eauto.
Qed.

Global Program Instance ModSem_Ref_PreOrder: PreOrder ((⊑)).
Next Obligation.
  ii; ss.
Qed.
Next Obligation.
  ii. eapply H0. eapply H; ss.
Qed.

Global Program Instance ModSem_EpsFacts: EpsFacts.
Next Obligation.
  upt. des_ifs. refl.
Qed.
Next Obligation.
  upt. des_ifs. refl.
Qed.
Next Obligation.
  upt. des_ifs.
Qed.

(*
a ⊑ a'
b ⊑ b'
a + b ⊑ a' + b'

∀ c. (c + a) ⊑B (c + a')
∀ c. (c + b) ⊑B (c + b')
∀ c. (c + a + b) ⊑B (c + a' + b')



Q: should a ⊑ a' denote both
(1) ∀ c. (c + a) ⊑B (c + a')
and
(2) a ⊑B a'
?

Even without proper ε, we can derive (2) from (1) using ε' with the following:
ε' + a ⊒⊑B a.

Let us try without proper ε, and see what happens
TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTttt
*)
Global Program Instance ModSem_RefFacts: RefFacts (T:=ModSem.t).
Next Obligation.
  do 3 r. i.
  unfold ref, ModSem.ref in *.
  i. rewrite oplus_assoc_weak. rewrite H0.
  rewrite oplus_comm_weak. rewrite oplus_assoc_weak. rewrite H.
  rewrite oplus_assoc_weak2. rewrite oplus_comm_weak.
  rewrite oplus_assoc_weak2. refl.
Qed.

Global Program Instance ModSem_EquivFacts: EquivFacts (T:=ModSem.t).
Next Obligation.
  econs.
  - ii. upt. des_ifs; try refl.
  - ii. upt. des_ifs; try sym; et.
  - ii. upt. des_ifs; etrans; et.
Qed.

Global Program Instance pointed_equiv_Proper `{Equiv T}: Proper ((≡) ==> (≡)) just.
Next Obligation. ii. upt. ss. Qed.

Global Program Instance pointed_ref_Proper `{Ref T}: Proper ((⊑) ==> (⊑)) just.
Next Obligation. do 3 r. i. ss. Qed.

Global Program Instance pointed_ref_both_Proper `{Ref T}: Proper ((⊒⊑) ==> (⊒⊑)) just.
Next Obligation. ii. upt. ss. Qed.

Global Program Instance ModSem_MRA: MRA.t := {
  car := ModSem.t;
}.
Next Obligation.
  econs.
  - i. cut ( | |a| | ≡ |a| ).
    { intro T. rewrite T. refl. }
    upt. des_ifs; try refl. erewrite ModSem.core_idemp. refl.
  - i. upt. des_ifs; try refl. erewrite ModSem.core_oplus. refl.
  - ii. upt. des_ifs. rr in H.  rr. des. esplits; et.
    eapply Forall2_apply_Forall2; et. ii. ss. des_ifs. ss. des. clarify.
    esplits; ss. ii.
  (* (| i1 |) x ≈ (| i2 |) x *)
    admit "ez".
Qed.
Next Obligation.
  do 2 r. i. upt. des_ifs; ss; clear_tac.
  - eapply ModSemPair.adequacy_whole. ss.
    econs.
    { instantiate (1:=top2). ss. }
    2: { instantiate (2:=unit). instantiate (1:=fun _ '(st_src, st_tgt) => exists ste, st_tgt = Any.pair st_src ste).
         ss. esplits; ss; et. }
    i. ss. esplits; et.
    { rewrite in_app_iff. left. rewrite in_map_iff. esplits; et. ss. }
    ii. des_u. clarify. des. subst.
    abstr (f_src y) itr. clear_tac. clear FINDS. clear_tac.
    eapply sim_itree_fsubset with []; ss.
    {
      clear_tac. revert mrs_src ste itr. ginit. gcofix CIH. i.
      ides itr; my_steps.
      + rr. esplits; ss; et.
      + gstep. econs; et. gbase. eapply CIH.
      + destruct e.
        { destruct c; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
        destruct s.
        { destruct p; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
        { destruct e; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
    }
  - eapply ModSemPair.adequacy_unit.
Qed.
Next Obligation.
  upt. des_ifs; ss; try refl.
  eapply ModSemPair.adequacy. ss.
  econs.
  { instantiate (1:=top2). ss. }
  2: { instantiate (2:=unit). instantiate (1:=fun _ '(st_src, st_tgt) => exists _st, st_src = Any.pair st_tgt _st).
       ss. esplits; ss; et. }
  i. ss. rewrite List.map_map in *. rewrite in_app_iff in *. des.
  { rewrite in_map_iff in *. des. destruct x as [fn0 itr]; ss. clarify.
    esplits; et.
    ii. des; subst. des_u. abstr (itr y) itr0.
    clear FINDS0. clear_tac.
    eapply sim_itree_fsubset with []; ss.
    {
      clear_tac. revert mrs_tgt _st itr0. ginit. gcofix CIH. i.
      ides itr0; my_steps.
      + rr. esplits; ss; et.
      + gstep. econs; et. gbase. eapply CIH.
      + destruct e.
        { destruct c; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
        destruct s.
        { destruct p; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
        { destruct e; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
    }
  }
  { rewrite in_map_iff in *. des. destruct x as [fn0 itr]; ss. clarify. esplits; et.
    ii. des; subst. des_u. unfold bar, ktree_Bar. abstr (itr y) itr0. unfold bar, itree_Bar.
    clear FINDS0. clear_tac.
    eapply sim_itree_fsubset with []; ss.
    {
      clear_tac. revert mrs_tgt _st itr0. ginit. gcofix CIH. i.
      ides itr0; my_steps.
      + rr. esplits; ss; et.
      + gstep. econs; et. gbase. eapply CIH.
      + destruct e.
        { destruct c; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
        destruct s.
        { destruct p; rewrite <- ! bind_trigger; resub; my_steps.
          - (*** FIXME ***) unfold core_h. unfold triggerUB. my_steps.
          - (*** FIXME ***) unfold core_h. unfold triggerUB. my_steps.
        }
        { destruct e; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
    }
  }
Qed.

End FACTS.
