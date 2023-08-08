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
Require Import LSimModSem.

Set Implicit Arguments.


Section FACTS.

Global Program Instance ModSem_OPlusFactsWeak: OPlusFactsWeak (T:=ModSem.t).
Next Obligation.
  eapply ModSemPair.adequacy.
  destruct a as [a|]; ss.
  2: { upt. des_ifs; ss. refl. }
  destruct b as [b|]; ss.
  2: { upt. des_ifs; ss. refl. }
  econs.
  { instantiate (1:=top2). ss. }
  2: { instantiate (2:=unit).
       instantiate (1:=fun _ '(st_src, st_tgt) => exists st0 st1, st_tgt = Any.pair st0 st1 /\ st_src = Any.pair st1 st0).
       ss. esplits; et. ss. }
  i. ss. rewrite in_app_iff in FINDS. des.
  - rewrite in_map_iff in *. des; ss. destruct x; ss. clarify.
    esplits; et.
    { rewrite in_app_iff. right. rewrite in_map_iff. esplits; et. ss. }
    admit "ez".
  - rewrite in_map_iff in *. des; ss. destruct x; ss. clarify.
    esplits; et.
    { rewrite in_app_iff. left. rewrite in_map_iff. esplits; et. ss. }
    admit "ez".
    Unshelve.
Qed.
Next Obligation.
  eapply ModSemPair.adequacy.
  destruct a as [a|]; ss.
  2: { upt. des_ifs; ss; refl. }
  destruct b as [b|]; ss.
  2: { upt. des_ifs; ss; refl. }
  destruct c as [c|]; ss.
  2: { upt. des_ifs; ss; refl. }
  econs; eauto.
  { instantiate (1:=top2). ss. }
  2: { instantiate (2:=unit).
       instantiate (1:=fun _ '(st_src, st_tgt) => exists st0 st1 st2,
                           st_tgt = (Any.pair st0 (Any.pair st1 st2)) /\ st_src = (Any.pair (Any.pair st0 st1) st2)).
       ss. esplits; et. ss. }
  i. ss. rewrite in_app_iff in FINDS. des.
  2: {
    rewrite in_map_iff in *. des; ss. destruct x; ss. clarify.
    esplits; et.
    { rewrite in_app_iff. right. rewrite in_map_iff. eexists (_, _); ss. esplits; et. rewrite in_app_iff. right; ss.
      rewrite in_map_iff. esplits; et. ss.
    }
    admit "ez".
  }
  rewrite in_map_iff in *. des. destruct x; ss; clarify. rewrite in_app_iff in *. des.
  {
    rewrite in_map_iff in *. des; ss. destruct x; ss. clarify.
    esplits; et.
    { rewrite in_app_iff. left. rewrite in_map_iff. esplits; et. ss.
    }
    admit "ez".
  }
  {
    rewrite in_map_iff in *. des; ss. destruct x; ss. clarify.
    esplits; et.
    { rewrite in_app_iff. right. rewrite in_map_iff. eexists (_, _); ss. esplits; et. rewrite in_app_iff. left; ss.
      rewrite in_map_iff. esplits; et. ss.
    }
    admit "ez".
  }
Qed.
Next Obligation.
  ii.
  upt. des_ifs.
  rr in H. des. rr in H0. des. rr. ss. esplits; et.
  2: { congruence. }
  eapply Forall2_app.
  - eapply Forall2_apply_Forall2; et. ii; ss. des_ifs. ss. des; clarify. esplits; et.
    ii. unfold focus_left. rewrite H4. refl.
  - eapply Forall2_apply_Forall2; et. ii; ss. des_ifs. ss. des; clarify. esplits; et.
    ii. unfold focus_right. rewrite H4. refl.
Qed.

Global Program Instance ModSem_equiv_ref: subrelation ((≡)) (⊑).
Next Obligation.
  r; i. eapply ModSemPair.adequacy.
  destruct x as [x|].
  2: { upt. des_ifs. }
  destruct y as [y|].
  2: { upt. des_ifs. }
  upt. ss. destruct H as [T U].
  econs; ss.
  { instantiate (1:=top2). ss. }
  2: { instantiate (2:=unit).
       instantiate (1:=fun _ '(st_src, st_tgt) => st_src = st_tgt). ss. }
  i. ss.
  eapply Forall2_In_r in FINDS; et. des. des_ifs. des; ss. clarify.
  esplits; et.
  admit "ez - eutt".
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

Global Program Instance ModSem_MRA: MRA.t := {
  car := ModSem.t;
}.
Next Obligation.
  econs.
  - ii. upt. des_ifs; try refl.
  - ii. upt. des_ifs; try sym; et.
  - ii. upt. des_ifs; etrans; et.
Qed.
Next Obligation.
  econs.
  - i. upt. des_ifs.
    + eapply equiv_ref_both. erewrite ModSem.core_idemp.
      r. esplits.
      { erewrite ModSem.core_idemp. ii. upt. des_ifs; try refl.
  - ii. upt. des_ifs; try sym; et.
  - ii. upt. des_ifs; etrans; et.
Qed.

End FACTS.
