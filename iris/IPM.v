Require Import Algebra Coqlib.
Require Import String.
Set Implicit Arguments.
Open Scope string_scope.
Open Scope list_scope.

Module MRAS.

  Class t: Type := {
    car:> Type;
    equiv:> Equiv car;
    oplus:> OPlus car;
    ref:> Ref car;
    bar:> Bar car;
    eps:> Eps car;
    equiv_facts:> EquivFacts (T:=car);
    ref_facts:> RefFacts (T:=car);
    oplus_facts:> OPlusFacts (T:=car);
    bar_facts:> BarFacts (T:=car);
    eps_facts:> EpsFacts (T:=car);
    affinity: forall a, a ⊑ ε;
    bar_intro: forall a, a ⊑ a ⊕ |a|;
  }.

End MRAS.

Global Instance equiv_relaxed `{M: MRA.t}: Equiv _ | 100
  := fun a b => a ⊒⊑ b /\ |a| ⊒⊑ |b|.

Global Program Instance MRA_to_MRAS (M: MRA.t): MRAS.t := {
  car := MRA.car;
  equiv := equiv_relaxed;
}.
Next Obligation.
  econs.
  - ii; ss. rr. esplits; refl.
  - ii; ss. rr in H. des. rr. esplits; sym; et.
  - ii; ss. rr in H. rr in H0. des. rr. esplits; etrans; et.
Qed.
Next Obligation.
  econs; try typeclasses eauto.
  ii. rr in H. des; ss. eapply H.
Qed.
Next Obligation.
  econs; try typeclasses eauto.
  - ii. rr. esplits; et.
    + r. esplits; eapply oplus_comm_weak.
    + rewrite ! bar_oplus_weak. r. esplits; eapply oplus_comm_weak.
  - ii. rr. esplits; et.
    + r. esplits; try eapply oplus_assoc_weak; try eapply oplus_assoc_weak2.
    + rewrite ! bar_oplus_weak. r.
      esplits; try eapply oplus_assoc_weak; try eapply oplus_assoc_weak2.
  - ii. rr in H. rr in H0. des. rr. esplits; et.
    + rewrite H. rewrite H0. refl.
    + rewrite ! bar_oplus_weak.
      rewrite H1. rewrite H2. refl.
Qed.
Next Obligation.
  econs; try typeclasses eauto.
  - ii. rr. esplits; et.
    + rewrite bar_idemp_weak. refl.
    + rewrite bar_idemp_weak. refl.
  - ii. rr. esplits.
    + rewrite bar_oplus_weak. refl.
    + rewrite bar_idemp_weak. rewrite ! bar_oplus_weak.
      rewrite ! bar_idemp_weak.
      refl.
  - ii. rr in H. des. rr. esplits; et.
    + rewrite ! bar_idemp_weak. ss.
Qed.
Next Obligation.
  econs; try typeclasses eauto.
  - ii. rr. esplits; et.
    + rewrite eps_r. refl.
    + rewrite bar_oplus_weak. rewrite eps_bar. rewrite eps_r. refl.
  - ii. rr. esplits; et.
    + rewrite eps_l. refl.
    + rewrite bar_oplus_weak. rewrite eps_bar. rewrite eps_l. refl.
  - rr. esplits; try rewrite ! eps_bar; refl.
Qed.
Next Obligation.
  eapply MRA.affinity.
Qed.
Next Obligation.
  eapply MRA.bar_intro.
Qed.

Global Program Instance hat_Proper `{MRA.t}: Proper ((≡) ==> equiv_relaxed) (fun x => x).
Next Obligation.
  ii. rr. esplits.
  - rewrite H0. refl.
  - rewrite H0. refl.
Qed.

Definition incl `{OPlus T, Equiv T}: T -> T -> Prop :=
  fun a b => exists ctx, (a ⊕ ctx) ≡ b.
Notation "(≼)" := (incl) (at level 50).
Notation "x ≼ y" := (incl x y) (at level 50).

Section INCLFACTS.
  (* Context `{OPlus T, Equiv T, Eps T, Bar T, !EquivFacts, !EpsFacts}. *)
  Context `{M: MRAS.t}.

  Global Program Instance incl_sub :
    subrelation ((≡)) ((≼)).
  Next Obligation.
    ii; ss. r. exists ε. rewrite eps_r. ss.
  Qed.

  Global Program Instance incl_Proper: Proper ((≡) ==> (≡) ==> impl) ((≼)).
  Next Obligation.
    ii; ss. r in H1. r. des. rewrite H in H1. rewrite H0 in H1. et.
  Qed.

  Global Program Instance extends_PreOrder: PreOrder ((≼)).
  Next Obligation.
    ii. rr. esplits; et. rewrite eps_r. refl.
  Qed.
  Next Obligation.
    unfold incl. ii. des. esplits; et. setoid_subst. rewrite CM.add_assoc. f_equal; et.
  Qed.

  Global Program Instance add_extends: Proper ((≼) ==> (≼) ==> (≼)) (⋅).
  Next Obligation.
    unfold CM.extends.
    ii. des. setoid_subst. esplits; et. rewrite <- ! CM.add_assoc. f_equal.
    instantiate (1:=ctx0 ⋅ ctx).
    rewrite ! CM.add_assoc. f_equiv.
    rewrite <- ! CM.add_assoc. f_equiv.
    rewrite CM.add_comm. f_equiv.
  Qed.

Lemma unit_idl: ∀ a, ε ⋅ a ≡ a. Proof. i. rewrite add_comm. rewrite unit_id. ss. Qed.

Lemma unit_extends: ∀ x, ε ≼ x.
Proof.
  ii. r. esplits. rewrite unit_idl. refl.
Qed.







From iris.bi Require Import derived_connectives updates.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
Require Export DisableSsreflect.
Arguments Z.of_nat: simpl nomatch.

