Require Import Coqlib Mod ModSem Algebra Any Skeleton AList.
Require Export WrapModSem.
Require Import ModFacts ModSemFacts.
From stdpp Require Import base gmap.

Set Implicit Arguments.

Section WRAP.

  Context `{Sk.ld}.

  Global Program Instance wrap_mod: Wrap conds (Mod.t) :=
    fun cs md => Mod.mk (fun sk => 𝑤_{cs} (md.(Mod.get_modsem) sk)) md.(Mod.sk) _ _.
  Next Obligation.
    i. ss. erewrite Mod.get_modsem_Proper; et.
  Qed.
  Next Obligation.
    i. ss. erewrite Mod.get_modsem_affine; et. refl.
  Qed.

End WRAP.

Section WRAPFACTS.

Context `{Sk.ld}.
Opaque MRA.car.

Obligation Tactic := idtac.
Global Program Instance Hoare_WA: WA.t (H:=Mod_MRA.(MRA.equiv)) (S:=conds_CM) | 50 := {
  morph := wrap_mod;
}.
Next Obligation.
  ii. ss. rr. esplits; ss. ii. rewrite ! (WA.morph_oplus (t:=Hoare_WA_ModSem)). refl.
Qed.
Next Obligation.
  ii. ss. rr. esplits; ss. ii. rewrite ! (WA.morph_unit (t:=Hoare_WA_ModSem)). refl.
Qed.
Next Obligation.
  ii. ss.
Qed.
Next Obligation.
  ii. ss. subst. rr in H1. des; ss. rr. esplits; ss. ii. eapply (WA.morph_Proper1 (t:=Hoare_WA_ModSem)); ss.
Qed.

Global Program Instance Mod_WrapBar: WrapBarCommute (T:=Mod.t) | 150.
Next Obligation.
  i. rr. esplits; ss. ii. eapply wrap_bar.
Qed.

End WRAPFACTS.
