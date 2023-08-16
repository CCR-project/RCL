Require Import Coqlib Algebra.
Require Export sflib.
Require Export ITreelib.
Require Export ModSem ModSemE ModSemFacts.
Export Events.
Require Export AList.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Permutation.

Set Implicit Arguments.


Module Mod.
Section MOD.
  Context `{Sk.ld}.

  Record t: Type := mk {
    get_modsem: Sk.t -> ModSem.t;
    sk: Sk.t;
    enclose: ModSem.t := (get_modsem sk);
    (* get_modsem_Proper:> Proper ((≡) ==> eq) get_modsem; *)
    get_modsem_Proper:> forall sk0 sk1 (EQV: sk0 ≡ sk1) (WF: Sk.wf sk0), get_modsem sk0 = get_modsem sk1;
    get_modsem_affine:> forall sk0 sk1 (EQV: Sk.extends sk0 sk1) (WF: Sk.wf sk1), get_modsem sk1 ⊑ get_modsem sk0;
    get_modsem_affine_core:> forall sk0 sk1 (EQV: Sk.extends sk0 sk1) (WF: Sk.wf sk1), | get_modsem sk1 | ⊑ | get_modsem sk0 |;
  }
  .

  Definition wf (md: t): Prop := (<<SK: Sk.wf (md.(sk))>>).
  (* Definition wf (md: t): Prop := (<<WF: ModSem.wf md.(enclose)>> /\ <<SK: Sk.wf (md.(sk))>>). *)

  Global Program Instance bar: Bar t := fun (md: t) => mk (fun sk => |(md.(get_modsem) sk)| ) Sk.unit _ _ _.
  Next Obligation.
    erewrite get_modsem_Proper; et.
  Qed.
  Next Obligation.
    rewrite get_modsem_affine_core; et. refl.
  Qed.
  Next Obligation.
    erewrite (@bar_idemp_weak).
    2: { eapply ModSem_MRA. }
    erewrite (@bar_idemp_weak).
    2: { eapply ModSem_MRA. }
    rewrite get_modsem_affine_core; et. refl.
  Qed.

  Section BEH.

  Context {CONF: EMSConfig}.

  Definition compile (md: t): semantics :=
    if excluded_middle_informative (wf md)
    then ModSem.compile' md.(enclose)
    else semantics_NB
  .

  (* Record wf (md: t): Prop := mk_wf { *)
  (*   wf_sk: Sk.wf md.(sk); *)
  (* } *)
  (* . *)
  (*** wf about modsem is enforced in the semantics ***)

  Global Program Instance oplus: OPlus t := fun (md0 md1: t) => {|
    get_modsem := fun sk => (md0.(get_modsem) sk) ⊕ (md1.(get_modsem) sk);
    sk := md0.(sk) ⊕ md1.(sk);
  |}
  .
  Next Obligation.
    ii. rewrite ! (@get_modsem_Proper _ _ _ EQV); et.
  Qed.
  Next Obligation.
    rewrite (get_modsem_affine _ EQV); et.
    rewrite (get_modsem_affine _ EQV); et.
    refl.
  Qed.
  Next Obligation.
    erewrite (@bar_oplus_weak).
    2: { eapply ModSem_MRA. }
    erewrite (@bar_oplus_weak).
    2: { eapply ModSem_MRA. }
    rewrite (get_modsem_affine_core _ EQV); et.
    rewrite (get_modsem_affine_core _ EQV); et.
    refl.
  Qed.

  Global Program Instance eps: Eps t := {|
    get_modsem := fun _ => ε;
    sk := Sk.unit;
  |}.
  Next Obligation. refl. Qed.
  Next Obligation. refl. Qed.

  Global Program Instance equiv: Equiv t :=
    fun md0 md1 => md0.(sk) ≡ md1.(sk) /\ forall sk0, md0.(get_modsem) sk0 = md1.(get_modsem) sk0
  .

  Global Program Instance equiv_Equiv: EquivFacts.
  Next Obligation.
    econs.
    - ii; ss. rr. esplits; refl.
    - ii; ss. rr in H0; des. rr. esplits; sym; try apply H0; et.
    - ii; ss. rr in H0; rr in H1; des. rr. esplits; (etrans; [try apply H0|try apply H1]; et).
  Qed.

  End BEH.

  Section REFINE.

  Global Program Instance refb: RefB t :=
    fun md_tgt md_src =>
      (* (<<REF: forall `{EMSConfig} tr, (Sk.wf md_tgt.(sk) /\ Beh.of_program (compile md_tgt) tr) -> *)
      (*                                 (Sk.wf md_src.(sk) /\ Beh.of_program (compile md_src) tr)>>) *)
      (<<REF: forall `{EMSConfig}, Beh.of_program (compile md_tgt) <1= Beh.of_program (compile md_src)>>)
  .

  Global Program Instance ref: Ref t :=
    fun ms_tgt ms_src =>
      forall (ctx: t), (ctx ⊕ ms_tgt) ⊑B (ctx ⊕ ms_src)
  .

  End REFINE.

  Lemma compile_not_wf
    `{EMSConfig}
    md tr
    (WF: ~ wf md)
    (TR: Beh.of_program (compile md) tr)
    :
    tr = Tr.nb
  .
  Proof.
    unfold compile in *. des_ifs; ss.
    - punfold TR. inv TR; ss; csc.
      + punfold SPIN. inv SPIN; ss; csc. des; subst. ss.
      + rr in STEP. des; ss.
  Qed.

End MOD.
End Mod.
