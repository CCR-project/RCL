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
  assert(T: Sk.wf (Mod.sk md1) = Sk.wf (Mod.sk md0)).
  { eapply prop_ext. split; eapply Sk.wf_equiv; et. sym; et. }
  { ii. des. do 2 r in SEM. unfold Mod.enclose in *. unfold ModSem.compile' in *.
    specialize (SEM md0.(Mod.sk) H0 (Mod.wf md0) tr).
    unfold Mod.compile in *. unfold Mod.enclose in *. unfold Mod.wf in *.
    rewrite T. erewrite Mod.get_modsem_Proper; et.
    { sym; et. }
    { rewrite T; et. }
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

Global Program Instance Mod_ref_refB: subrelation (⊑) ((⊑B)).
Next Obligation.
  ii. rr in H. des. specialize (H ε _ tr). ss.
  exploit H; et.
  { clear H.
    rewrite Sk.add_unit_l. esplits; ss.
    unfold Mod.compile, Mod.enclose in *. ss. rewrite Sk.add_unit_l. upt. ss.
    des_ifs; et. unfold Mod.wf in *. ss. rewrite Sk.add_unit_l. ss.
  }
  intro T; des.
  rewrite Sk.add_unit_l in T. esplits; ss. clear - T0.
  unfold Mod.compile, Mod.enclose in *. ss. rewrite Sk.add_unit_l in T0. upt. ss.
  des_ifs; et. unfold Mod.wf in *. ss. rewrite Sk.add_unit_l in T0. ss.
Qed.

Global Program Instance ModSem_RefBFacts: RefBFacts.
Next Obligation.
  econs.
  - ii; ss.
  - ii. eapply H0. eapply H; ss.
Qed.
Next Obligation.
  ii. des. rr in H. des. esplits; et.
  - rewrite <- H. ss.
  - unfold Mod.compile, Mod.enclose in *. ss. rewrite H3 in *. erewrite <- Mod.get_modsem_Proper; et. des_ifs.
    unfold Mod.wf in *. admit "Remove P".
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
  rr. ss. rewrite Sk.add_unit_r. esplits; try refl. ii. upt. des_ifs.
Qed.
Next Obligation.
  rr. ss. rewrite Sk.add_unit_l. esplits; try refl. ii. upt. des_ifs.
Qed.
Next Obligation.
  rr. ss. esplits; try refl.
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
  ii. des. ss. rr in H. des. esplits; et.
  - rewrite <- H. ss.
  - unfold Mod.compile in *. ss.
    erewrite <- (Mod.get_modsem_Proper ctx); et.
    2: { rewrite H; refl. }
    erewrite <- (Mod.get_modsem_Proper y); et.
    2: { rewrite H. refl. }
    rewrite <- H3. des_ifs.
    unfold Mod.wf in *.
    admit "Remove P".
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
  ii. des. ss. rewrite Sk.add_unit_r. esplits.
  { eapply Sk.wf_mon; et. rr. esplits; refl. }
  assert(T:=MRA.affinity). ss. do 4 r in T. ss.
  rewrite <- ModSem_Mod_compile in H1. ss. eapply T in H1. clear T.
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
  ii. des. ss. esplits; ss.
  { rewrite Sk.add_unit_r; ss. }
  assert(U: (Mod.get_modsem a (Mod.sk ctx ⊕ Mod.sk a)) ⊑ (Mod.get_modsem (a ⊕ |a| ) (Mod.sk ctx ⊕ Mod.sk a))).
  { ss.
    etrans.
    { erewrite (MRA.bar_intro (t:=ModSem_MRA)). refl. }
    refl.
  }
  eapply ModSem_ref_refB in U. unfold Mod.compile, Mod.enclose. ss. rewrite Sk.add_unit_r. des_ifs.
  { upt. des_ifs. eapply U.
  }
  assert(U: (Mod.get_modsem (ctx ⊕ a) (Mod.sk ctx ⊕ Mod.sk a)) ⊑B (Mod.get_modsem (ctx ⊕ (a ⊕ |a| )) (Mod.sk ctx ⊕ Mod.sk a))).
  { rewrite MRA.bar_intro.
    rewrite Mod.get_modsem_affine; et; try refl.
    { rewrite Sk.add_unit_r. rr. esplits; refl. }
  }
  { eapply Sk.wf_mon; et. rr. esplits; refl. }
  assert(T:=MRA.affinity). ss. do 4 r in T. ss.
  rewrite <- ModSem_Mod_compile in H1. ss. eapply T in H1. clear T.
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
  ii. des. ss. rewrite Sk.add_unit_r. esplits.
  { eapply Sk.wf_mon; et. rr. esplits; refl. }
  assert(T:=MRA.affinity). ss. do 4 r in T. ss.
  rewrite <- ModSem_Mod_compile. ss. eapply T. clear T.
  rewrite <- ModSem_Mod_compile in H1. ss.
  replace (Mod.wf (ctx ⊕ ε)) with (Mod.wf (ctx ⊕ a)) by admit "Remove P".
  eapply Mod.get_modsem_affine; et.
  { rr. esplits. rewrite Sk.add_comm. refl. }
  2: {
  rewrite Sk.add_unit_r. rp; et.
  rr.
  upt.
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
