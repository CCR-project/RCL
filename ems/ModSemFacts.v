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
  (* sim_fsem *)
  (*   (List.map (map_snd (fun ktr : Any.t -> itree Es Any.t => focus_left (T:=Any.t) ∘ ktr)) (ModSem.fnsems a) ++ *)
  (*    List.map (map_snd (fun ktr : Any.t -> itree Es Any.t => focus_right (T:=Any.t) ∘ ktr)) (ModSem.fnsems b)) *)
  (*   (fun (_ : ()) '(st_src, st_tgt) => exists st0 st1 : Any.t, st_tgt = Any.pair st0 st1 /\ st_src = Any.pair st1 st0) top2 *)
  (*   (focus_left (T:=Any.t) ∘ i) (focus_right (T:=Any.t) ∘ i) *)
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
  (* sim_fsem *)
  (*   (fun (_ : ()) '(st_src, st_tgt) => *)
  (*    exists st0 st1 st2 : Any.t, st_tgt = Any.pair st0 (Any.pair st1 st2) /\ st_src = Any.pair (Any.pair st0 st1) st2) top2 *)
  (*   (focus_right (T:=Any.t) ∘ i) (focus_right (T:=Any.t) ∘ (focus_right (T:=Any.t) ∘ i)) *)
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
  ii. subst. des_u. eapply eutt_sim_itree. sym; ss.
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
    admit "ez".
  (* sim_itree *)
  (*   (List.map (map_snd (fun ktr : Any.t -> itree Es Any.t => focus_left (T:=Any.t) ∘ ktr)) (ModSem.fnsems t) ++ *)
  (*    List.map (map_snd (fun ktr : Any.t -> itree Es Any.t => focus_right (T:=Any.t) ∘ ktr)) (ModSem.fnsems t0)) *)
  (*   (fun (_ : ()) '(st_src, st_tgt) => exists ste0 : Any.t, st_tgt = Any.pair st_src ste0) top2 false false ()  *)
  (*   (mrs_src, itr) (Any.pair mrs_src ste, focus_left itr) *)
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
  (* sim_fsem (ModSem.fnsems t) (fun (_ : ()) '(st_src, st_tgt) => exists _st : Any.t, st_src = Any.pair st_tgt _st) top2 *)
  (*   (focus_left (T:=Any.t) ∘ itr) itr *)
    admit "ez". }
  { rewrite in_map_iff in *. des. destruct x as [fn0 itr]; ss. clarify. esplits; et.
  (* sim_fsem (ModSem.fnsems t) (fun (_ : ()) '(st_src, st_tgt) => exists _st : Any.t, st_src = Any.pair st_tgt _st) top2 *)
  (*   (focus_right (T:=Any.t) ∘ (| itr |)) itr *)
    admit "ez". }
Qed.

End FACTS.
