Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import ModSem Mod SimModSem.
Require Import Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import Any.

Set Implicit Arguments.

Local Open Scope nat_scope.



Module ModPair.
Section SIMMOD.
  Context `{LD: Sk.ld}.
  Variable (md_src md_tgt: Mod.t).
  Inductive sim: Prop := mk {
    sim_modsem:
      forall sk_src sk_tgt
             (EXT: Sk.extends sk_src sk_tgt)
             (SKWF: Sk.wf (sk_tgt ⊕ md_tgt.(Mod.sk))),
        <<SIM: ModSemPair.sim (md_src.(Mod.get_modsem) (sk_src ⊕ md_src.(Mod.sk)))
                 (md_tgt.(Mod.get_modsem) (sk_tgt ⊕ md_tgt.(Mod.sk)))>>;
    sim_sk: Sk.extends md_src.(Mod.sk) md_tgt.(Mod.sk);
  }.

End SIMMOD.

Section FACTS.

Context `{LD: Sk.ld}.

Theorem compose
  md_src0 md_tgt0 md_src1 md_tgt1
  (SIM0: ModPair.sim md_src0 md_tgt0)
  (SIM1: ModPair.sim md_src1 md_tgt1)
  :
  <<SIM: ModPair.sim (md_src0 ⊕ md_src1) (md_tgt0 ⊕ md_tgt1)>>
.
Proof.
  inv SIM0.
  inv SIM1.
  des.
  econs; ss.
  2:{ i. rewrite sim_sk0. rewrite sim_sk1. refl. }
  ii; ss.
  eapply ModSemPair.compose; et.
  - assert(T: sk_src ⊕ (Mod.sk md_src0 ⊕ Mod.sk md_src1) ≡ (sk_src ⊕ Mod.sk md_src1) ⊕ Mod.sk md_src0).
    { rewrite <- ! Sk.add_assoc. eapply Sk.add_equiv; try refl. eapply Sk.add_comm; et. }
    erewrite (Mod.get_modsem_Proper md_src0); try eapply T.
    2: { eapply Sk.wf_mon; et. rewrite sim_sk0. rewrite sim_sk1. rewrite EXT. refl. }
    assert(U: sk_tgt ⊕ (Mod.sk md_tgt0 ⊕ Mod.sk md_tgt1) ≡ (sk_tgt ⊕ Mod.sk md_tgt1) ⊕ Mod.sk md_tgt0).
    { rewrite <- ! Sk.add_assoc. eapply Sk.add_equiv; try refl. eapply Sk.add_comm; et. }
    erewrite (Mod.get_modsem_Proper md_tgt0); try eapply U.
    2: { ss. }
    eapply sim_modsem0; ss.
    2: { rewrite <- U; et. }
    rewrite EXT. rewrite sim_sk1. refl.
  - assert(T: sk_src ⊕ (Mod.sk md_src0 ⊕ Mod.sk md_src1) ≡ (sk_src ⊕ Mod.sk md_src0) ⊕ Mod.sk md_src1).
    { rewrite <- ! Sk.add_assoc. eapply Sk.add_equiv; try refl. }
    erewrite (Mod.get_modsem_Proper md_src1); try eapply T.
    2: { eapply Sk.wf_mon; et. rewrite sim_sk0. rewrite sim_sk1. rewrite EXT. refl. }
    assert(U: sk_tgt ⊕ (Mod.sk md_tgt0 ⊕ Mod.sk md_tgt1) ≡ (sk_tgt ⊕ Mod.sk md_tgt0) ⊕ Mod.sk md_tgt1).
    { rewrite <- ! Sk.add_assoc. eapply Sk.add_equiv; try refl. }
    erewrite (Mod.get_modsem_Proper md_tgt1); try eapply U.
    2: { ss. }
    eapply sim_modsem1; ss.
    2: { rewrite <- U; et. }
    rewrite EXT. rewrite sim_sk0. refl.
Qed.

Theorem adequacy
  md_src md_tgt
  (SIM: ModPair.sim md_src md_tgt)
  :
  md_tgt ⊑ md_src
.
Proof.
  ii. unfold Mod.compile, Mod.enclose in *.
  destruct (classic (Mod.wf (ctx ⊕ md_tgt))).
  2:{ eapply ModSem.compile_not_wf in PR; ss. subst. eapply Beh.nb_bottom. }
  pose (sk_tgt := (Mod.sk (ctx ⊕ md_tgt))).
  pose (sk_src := (Mod.sk (ctx ⊕ md_src))).
  destruct (classic (Sk.wf (Mod.sk md_tgt))); rename H0 into SKWF.
  2: { eapply ModSem.initial_itr_not_wf in PR; ss.
       { subst. eapply Beh.nb_bottom. }
       intro T. eapply SKWF. inv T; ss. eapply Sk.wf_mon; et. r. esplits; et.
       rewrite Sk.add_comm; et. refl. }
  (* assert (SKEQ: sk_tgt ≡ sk_src). *)
  (* { unfold sk_src, sk_tgt. ss. inv SIM. spc sim_sk0. rewrite sim_sk0. refl. } *)
  assert(EXT: Sk.extends sk_src sk_tgt).
  { subst sk_src sk_tgt. ss. inv SIM. rewrite sim_sk0. refl. }

  rr in H. unfold Mod.enclose in *. fold sk_src in H. des. inv WF.
  {
    folder.
    inv SIM. ss.
    exploit sim_modsem0.
    { refl. }
    { eauto. }
    intro T; des.
    eapply ModSemPair.adequacy; revgoals; et.
    2: {
      eapply ModSemPair.compose.
      - erewrite <- Mod.get_modsem_Proper; et; try by (eapply Sk.wf_equiv; [sym; et|]; ss).
      - eapply ModSemPair.self_sim.
      - eapply sim_modsem0; et.
        { r. subst sk_tgt. esplits. rewrite Sk.add_comm; refl. }
        rewrite SKEQ; ss.
    }
    { unfold Mod.wf, Mod.enclose. ii. ss. des; ss. folder. esplits; et.
      2: { rewrite SKEQ; ss. }
      {
        erewrite Mod.get_modsem_Proper; et; try by (eapply Sk.wf_equiv; [sym; et|]; ss).
        rewrite (Mod.get_modsem_Proper _ _ _ SKEQ); et; try by (eapply Sk.wf_equiv; [sym; et|]; ss).
        econs.
      }
    }
  }
Qed.

Corollary adequacy'
  `{EMSConfig}
  md_src md_tgt
  (SIM: ModPair.sim md_src md_tgt)
  :
  md_tgt ⊑ md_src
.
Proof.
  eapply adequacy; ss.
Qed.

End FACTS.
End ModPair.

