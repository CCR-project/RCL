Require Import Coqlib.
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
  ii. rr in H. des. rr in H0. des. rr. ss. esplits; et.
  2: { congruence. }
  eapply Forall2_app.
  - eapply Forall2_apply_Forall2; et. ii; ss. des_ifs. ss. des; clarify. esplits; et.
    ii. unfold focus_left. rewrite H4. refl.
  - eapply Forall2_apply_Forall2; et. ii; ss. des_ifs. ss. des; clarify. esplits; et.
    ii. unfold focus_right. rewrite H4. refl.
Qed.

Global Program Instance ModSem_Ref_PreOrder: PreOrder ((⊑)).
Next Obligation.
  ii; ss.
Qed.
Next Obligation.
  ii. eapply H0. eapply H; ss.
Qed.

(* Global Program Instance ModSem_EpsFacts: EpsFacts. *)
(* Next Obligation. *)
(*   ii; ss. *)
(* Qed. *)
(* Next Obligation. *)
(*   ii. eapply H0. eapply H; ss. *)
(* Qed. *)

Global Program Instance ModSem_RefFacts: RefFacts (T:=ModSem.t).
Next Obligation.
  do 3 r. i.
  {
    ii.
    eapply oplus_assoc_weak.
  }
  
  rewrite oplus_assoc_weak.
  rewrite H.
  - ii; ss.
  - ii. eapply H0. eapply H; ss.
Qed.

End FACTS.
