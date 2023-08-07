Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export ModSem ModSemE.
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
    get_modsem_extends:> forall sk0 sk1 (EQV: Sk.extends sk0 sk1) (WF: Sk.wf sk1), get_modsem sk1 ⊑ get_modsem sk0;
    get_modsem_extends_core:> forall sk0 sk1 (EQV: Sk.extends sk0 sk1) (WF: Sk.wf sk1), | get_modsem sk1 | ⊑ | get_modsem sk0 |;
  }
  .

  (* Definition wf (md: t): Prop := (<<SK: Sk.wf (md.(sk))>>). *)
  Definition wf (md: t): Prop := (<<WF: ModSem.wf md.(enclose)>> /\ <<SK: Sk.wf (md.(sk))>>).

  Program Definition core (md: t): t := mk (fun sk => |(md.(get_modsem) sk)| ) md.(sk) _ _ _.
  Next Obligation.
    erewrite get_modsem_Proper; et.
  Qed.
  Next Obligation.
    eapply get_modsem_extends_core; et.
  Qed.
  Next Obligation.
    rewrite ! ModSem.core_idemp.
    eapply get_modsem_extends_core; et.
  Qed.

  Global Program Instance bar: Bar t := core.

  Section BEH.

  Context {CONF: EMSConfig}.

  Definition compile (md: t): semantics :=
    ModSem.compile_itree (ModSem.initial_itr md.(enclose) (Some (wf md))).

  (* Record wf (md: t): Prop := mk_wf { *)
  (*   wf_sk: Sk.wf md.(sk); *)
  (* } *)
  (* . *)
  (*** wf about modsem is enforced in the semantics ***)

  Program Definition add (md0 md1: t): t := {|
    get_modsem := fun sk => (md0.(get_modsem) sk) ⊕ (md1.(get_modsem) sk);
    sk := md0.(sk) ⊕ md1.(sk);
  |}
  .
  Next Obligation.
    ii. rewrite ! (@get_modsem_Proper _ _ _ EQV); et.
  Qed.
  Next Obligation.
    admit "should hold".
  Qed.
  Next Obligation.
    admit "should hold".
  Qed.

  Global Program Instance add_OPlus: OPlus t := add.

  Program Definition empty: t := {|
    get_modsem := fun _ => ModSem.mk [] tt↑;
    sk := Sk.unit;
  |}
  .
  Next Obligation.
    ss.
  Qed.
  Next Obligation.
    ss.
  Qed.

  End BEH.

  Section REFINE.

  Definition cref' {CONF: EMSConfig} (md_tgt md_src: t): Prop :=
    forall (ctx: t), Beh.of_program (compile (ctx ⊕ md_tgt)) <1=
                       Beh.of_program (compile (ctx ⊕ md_src))
  .

  Definition cref (md_tgt md_src: t): Prop :=
    forall {CONF: EMSConfig}, cref' md_tgt md_src.

  Section CONF.
    Context {CONF: EMSConfig}.

    Global Program Instance cref_PreOrder: PreOrder cref.
    Next Obligation.
      ii. ss.
    Qed.
    Next Obligation.
      ii. eapply H0 in PR. eapply H1 in PR. eapply PR.
    Qed.

    Global Program Instance cref'_PreOrder: PreOrder cref'.
    Next Obligation. ii. ss. Qed.
    Next Obligation. ii. eapply H1. eapply H0. ss. Qed.
  End CONF.

  Definition bref {CONF: EMSConfig} (md_tgt md_src: t): Prop :=
    Beh.of_program (compile md_tgt) <1= Beh.of_program (compile md_src)
  .

  End REFINE.

End MOD.
End Mod.
