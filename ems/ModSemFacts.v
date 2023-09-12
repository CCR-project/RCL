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
Require Import SimModSem.

Set Implicit Arguments.



Ltac my_steps :=
  repeat (esplits; my_red_both;
          try (guclo sim_itree_indC_spec; first [apply sim_itree_indC_choose_tgt|apply sim_itree_indC_take_src|econs]; et);
          i; des; ss; subst; et).

Theorem bar_state_irr: forall ms0 ms1, ms0.(ModSem.fnsems) = ms1.(ModSem.fnsems) -> |just ms0| ⊑ |just ms1|.
Proof.
  i. eapply ModSemPair.adequacy. ss.
  econs.
  { instantiate (1:=top2). ss. }
  2: { instantiate (2:=unit).
       instantiate (1:=top2). ss. }
  i. esplits; ss.
  { rewrite H. et. }
  ii. subst. des_u.
  eapply sim_itree_fsubset with []; ss. clear_tac.
  rewrite in_map_iff in *. des; ss. destruct x; ss. clarify.
  clears fn. clear fn. clear_tac.
  unfold bar, ktree_Bar. ss.
  abstr (i y) itr. clear_tac.
  revert mrs_src mrs_tgt itr. ginit. gcofix CIH. i.
  ides itr; my_steps.
  + gstep. econs; et. gbase. eapply CIH.
  + destruct e; [destruct s|].
    { destruct c; rewrite <- ! bind_trigger; resub. my_steps; gstep; econs; et; gbase; eapply CIH. }
    { destruct p; rewrite <- ! bind_trigger; resub; my_steps.
      - unfold core_h. unfold triggerUB. my_steps.
      - unfold core_h. unfold triggerUB. my_steps. }
    { destruct e; rewrite <- ! bind_trigger; resub; my_steps; gstep; econsr; et; gbase; eapply CIH. }
Qed.

Section ALGEBRA.

Global Program Instance ModSem_OPlusFactsWeak: OPlusFactsWeak (T:=ModSem.t).
Next Obligation.
  i. eapply ModSemPair.adequacy.
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
    ii. des; subst. des_u. eapply sim_itree_fsubset with []; ss. clear_tac.
    clears b. clear b. clear_tac.
    abstr (i y) itr. clear_tac.
    revert st0 st1 itr. ginit. gcofix CIH. i.
    ides itr; my_steps.
    + rr. esplits; ss; et.
    + gstep. econs; et. gbase. eapply CIH.
    + destruct e; [destruct s|].
      { destruct c; rewrite <- ! bind_trigger; resub. my_steps; gstep; econs; et; gbase; eapply CIH. }
      { destruct p; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
      { destruct e; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
  - rewrite in_map_iff in *. des; ss. destruct x; ss. clarify.
    esplits; et.
    { rewrite in_app_iff. left. rewrite in_map_iff. esplits; et. ss. }
    ii. des; subst. des_u. eapply sim_itree_fsubset with []; ss. clear_tac.
    clears a. clear a. clear_tac.
    abstr (i y) itr. clear_tac.
    revert st0 st1 itr. ginit. gcofix CIH. i.
    ides itr; my_steps.
    + rr. esplits; ss; et.
    + gstep. econs; et. gbase. eapply CIH.
    + destruct e; [destruct s|].
      { destruct c; rewrite <- ! bind_trigger; resub. my_steps; gstep; econs; et; gbase; eapply CIH. }
      { destruct p; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
      { destruct e; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
Qed.
Next Obligation.
  i. eapply ModSemPair.adequacy.
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
  i. ss. rewrite in_app_iff in FINDS. des; revgoals.
  {
    rewrite in_map_iff in *. des; ss. destruct x; ss. clarify.
    esplits; et.
    { rewrite in_app_iff. right. rewrite map_app. rewrite in_app_iff. right. rewrite List.map_map. rewrite in_map_iff.
      eexists (_, _); esplits; ss; et. }
    ii. des; subst. des_u. eapply sim_itree_fsubset with []; ss. clear_tac.
    clears c. clear c. clear_tac.
    abstr (i y) itr. clear_tac.
    revert st0 st1 st2 itr. ginit. gcofix CIH. i.
    ides itr; my_steps.
    + rr. esplits; ss; et.
    + gstep. econs; et. gbase. eapply CIH.
    + destruct e; [destruct s|].
      { destruct c; rewrite <- ! bind_trigger; resub. my_red_both. (*** FIXME ***) rewrite focus_right_callE. my_steps.
        gstep; econs; et; gbase; eapply CIH. }
      { destruct p; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
      { destruct e; rewrite <- ! bind_trigger; resub;
          my_red_both; (*** FIXME ***) rewrite focus_right_eventE; my_steps; gstep; econs; et; gbase; eapply CIH.
      }
  }
  rewrite in_map_iff in *. des. destruct x; ss; clarify. rewrite in_app_iff in *. des.
  {
    rewrite in_map_iff in *. des; ss. destruct x; ss. clarify.
    esplits; et.
    { rewrite in_app_iff. left. rewrite in_map_iff. eexists (_, _); esplits; ss; et. }
    ii. des; subst. des_u. eapply sim_itree_fsubset with []; ss. clear_tac.
    clears a. clear a. clear_tac.
    abstr (i0 y) itr. clear_tac.
    revert st0 st1 st2 itr. ginit. gcofix CIH. i.
    ides itr; my_steps.
    + rr. esplits; ss; et.
    + gstep. econs; et. gbase. eapply CIH.
    + destruct e; [destruct s|].
      { destruct c; rewrite <- ! bind_trigger; resub. my_red_both. (*** FIXME ***) rewrite focus_left_callE. my_steps.
        gstep; econs; et; gbase; eapply CIH. }
      { destruct p; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
      { destruct e; rewrite <- ! bind_trigger; resub;
          my_red_both; (*** FIXME ***) rewrite focus_left_eventE; my_steps; gstep; econs; et; gbase; eapply CIH.
      }
  }
  {
    rewrite in_map_iff in *. des; ss. destruct x; ss. clarify.
    esplits; et.
    { rewrite in_app_iff. right. rewrite map_app. rewrite in_app_iff. left. rewrite List.map_map. rewrite in_map_iff.
      eexists (_, _); esplits; ss; et. }
    ii. des; subst. des_u. eapply sim_itree_fsubset with []; ss. clear_tac.
    clears b. clear b. clear_tac.
    abstr (i0 y) itr. clear_tac.
    revert st0 st1 st2 itr. ginit. gcofix CIH. i.
    ides itr; my_steps.
    + rr. esplits; ss; et.
    + gstep. econs; et. gbase. eapply CIH.
    + destruct e; [destruct s|].
      { destruct c; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
      { destruct p; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
      { destruct e; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
  }
Qed.
Next Obligation.
  ii.
  upt. des_ifs.
  rr in H. des. rr in H0. des. rr. ss. esplits; et.
  2: { congruence. }
  eapply Forall2_app.
  - eapply Forall2_apply_Forall2; et. ii; ss. des_ifs. ss. des; clarify. esplits; et.
    ii. cbn. unfold focus_left. rewrite H4. refl.
  - eapply Forall2_apply_Forall2; et. ii; ss. des_ifs. ss. des; clarify. esplits; et.
    ii. cbn. unfold focus_right. rewrite H4. refl.
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

Global Program Instance ModSem_Ref_PreOrder: PreOrder ((⊑@{ModSem.t})).
Next Obligation.
  ii; ss.
Qed.
Next Obligation.
  ii. eapply H0. eapply H; ss.
Qed.

Global Program Instance ModSem_EpsFacts: EpsFacts.
Next Obligation.
  i. upt. des_ifs.
Qed.
Next Obligation.
  i. upt. des_ifs.
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
  unfold sqsubseteq, ModSem.ref in *.
  i. rewrite oplus_assoc_weakl. rewrite H0.
  rewrite oplus_comm_weak. rewrite oplus_assoc_weakl. rewrite H.
  rewrite oplus_assoc_weakr. rewrite oplus_comm_weak.
  rewrite oplus_assoc_weakr. refl.
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

Global Program Instance pointed_ref_Proper `{Ref T}: Proper ((⊑@{ModSem.t}) ==> (⊑)) just.
Next Obligation. do 3 r. i. ss. Qed.

Global Program Instance pointed_ref_both_Proper `{Ref T}: Proper ((⊒⊑@{ModSem.t}) ==> (⊒⊑)) just.
Next Obligation. ii. upt. ss. Qed.

Global Program Instance ModSem_BarFacts: BarFacts (T:=ModSem.t).
Next Obligation.
  i. upt. des_ifs; try refl. erewrite ModSem.core_idemp. refl.
Qed.
Next Obligation.
  i. upt. des_ifs; try refl. erewrite ModSem.core_oplus. refl.
Qed.
Next Obligation.
  ii. upt. des_ifs. rr in H.  rr. des. esplits; et.
  eapply Forall2_apply_Forall2; et. ii. ss. des_ifs. ss. des. clarify.
  esplits; ss. ii.
  eapply bar_Proper. ss.
Qed.
Next Obligation.
  upt. des_ifs.
Qed.
  
Global Program Instance ModSem_MRA: MRA.t := {
  car := ModSem.t;
}.
Next Obligation.
  do 3 r. i. upt. des_ifs; ss; clear_tac.
  - eapply ModSemPair.adequacy_whole. ss.
    econs.
    { instantiate (1:=top2). ss. }
    2: { instantiate (2:=unit). instantiate (1:=fun _ '(st_src, st_tgt) => exists ste, st_tgt = Any.pair st_src ste).
         ss. esplits; ss; et. }
    i. ss. esplits; et.
    { rewrite in_app_iff. left. rewrite in_map_iff. esplits; et. ss. }
    ii. des_u. clarify. des. subst. cbn.
    abstr (f_src y) itr. clear_tac. clear FINDS. clear_tac.
    eapply sim_itree_fsubset with []; ss.
    {
      clear_tac. revert mrs_src ste itr. ginit. gcofix CIH. i.
      ides itr; my_steps.
      + rr. esplits; ss; et.
      + gstep. econs; et. gbase. eapply CIH.
      + destruct e; [destruct s|].
        { destruct c; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
        { destruct p; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
        { destruct e; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
    }
  - eapply ModSemPair.adequacy_unit.
Qed.
Next Obligation.
  i. upt. des_ifs; ss; try refl.
  eapply ModSemPair.adequacy. ss.
  econs.
  { instantiate (1:=top2). ss. }
  2: { instantiate (2:=unit). instantiate (1:=fun _ '(st_src, st_tgt) => exists _st, st_src = Any.pair st_tgt _st).
       ss. esplits; ss; et. }
  i. ss. rewrite List.map_map in *. rewrite in_app_iff in *. des.
  { rewrite in_map_iff in *. des. destruct x as [fn0 itr]; ss. clarify.
    esplits; et.
    ii. des; subst. cbn. des_u. abstr (itr y) itr0.
    clear FINDS0. clear_tac.
    eapply sim_itree_fsubset with []; ss.
    {
      clear_tac. revert mrs_tgt _st itr0. ginit. gcofix CIH. i.
      ides itr0; my_steps.
      + rr. esplits; ss; et.
      + gstep. econs; et. gbase. eapply CIH.
      + destruct e; [destruct s|].
        { destruct c; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
        { destruct p; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
        { destruct e; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
    }
  }
  { rewrite in_map_iff in *. des. destruct x as [fn0 itr]; ss. clarify. esplits; et.
    ii. des; subst. cbn. des_u. unfold bar, ktree_Bar. abstr (itr y) itr0.
    clear FINDS0. clear_tac.
    eapply sim_itree_fsubset with []; ss.
    {
      clear_tac. revert mrs_tgt _st itr0. ginit. gcofix CIH. i.
      ides itr0; my_steps.
      + rr. esplits; ss; et.
      + gstep. econs; et. gbase. eapply CIH.
      + destruct e; [destruct s|].
        { destruct c; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
        { destruct p; rewrite <- ! bind_trigger; resub; my_steps.
          - (*** FIXME ***) unfold core_h. unfold triggerUB. my_steps.
          - (*** FIXME ***) unfold core_h. unfold triggerUB. my_steps.
        }
        { destruct e; rewrite <- ! bind_trigger; resub; my_steps; gstep; econs; et; gbase; eapply CIH. }
    }
  }
Qed.

(* Require Import SimGlobalIndex SimGlobalIndexFacts. *)
(* From Ordinal Require Import Ordinal. *)
(* Global Program Instance refs_oplus_: Proper ((⊑S) ==> (⊑S) ==> (⊑S)) ((⊕)). *)
(* Next Obligation. *)
(*   ii. *)
(*   rr in H. rr in H0. des. rr. ss. esplits; ss. *)
(*   2: { congruence. } *)
(*   eapply Forall2_app. *)
(*   - eapply Forall2_apply_Forall2; et. clear. ii; ss. des_ifs. ss. clarify. ss. *)
(*     des; ss. subst. esplits; ss. *)
(*     ii. eapply simg_interp; et. *)
(*   - eapply Forall2_apply_Forall2; et. clear. ii; ss. des_ifs. ss. clarify. ss. *)
(*     des; ss. subst. esplits; ss. *)
(*     ii. eapply simg_interp; et. *)
(* Qed. *)

(* Global Program Instance refs_PreOrder_: PreOrder (⊑S). *)
(* Next Obligation. *)
(*   ii. rr. esplits; ss. *)
(*   eapply Forall2_impl. 2: { eapply Forall2_eq; ss. } i; ss. des_ifs. esplits; ss. *)
(*   i. *)
(*   ginit. *)
(*   guclo postcondC_spec. *)
(*   econs. *)
(*   2: { gfinal; right. eapply simg_refl. } *)
(*   i; ss. des; ss. *)
(* Qed. *)
(* Next Obligation. *)
(*   ii; ss. rr in H. rr in H0. des. rr. esplits; ss. *)
(*   2: { congruence. } *)
(*   eapply Forall2_impl. *)
(*   2: { eapply Forall2_trans; et. } *)
(*   clear. i; ss. des. des_ifs. des; ss. esplits; ss. *)
(*   { congruence. } *)
(*   i. eapply simg_trans; et. *)
(* Qed. *)

(* (*** TODO: put in Algebra.v ***) *)
(* Infix "⊑S@{ A }" := (@ref_strong A) (at level 50, only parsing). *)
(* Notation "⊑S@{ A }" := (@ref_strong A) (at level 50, only parsing). *)

(* Ltac upt := *)
(*   repeat match goal with *)
(*     | [H: context[@equiv _ (@Equiv_pointed _ _)] |- _] => unfold equiv, Equiv_pointed in H *)
(*     | [ |- context[@equiv _ (@Equiv_pointed _ _)]] => unfold equiv, Equiv_pointed *)
(*     | [H: context[@sqsubseteq _ (@Ref_pointed _ _)] |- _] => unfold sqsubseteq, Ref_pointed in H *)
(*     | [ |- context[@sqsubseteq _ (@Ref_pointed _ _)]] => unfold sqsubseteq, Ref_pointed *)
(*     | [H: context[@ref_strong _ (@RefStrong_pointed _ _)] |- _] => unfold ref_strong, RefStrong_pointed in H *)
(*     | [ |- context[@ref_strong _ (@RefStrong_pointed _ _)]] => unfold ref_strong, RefStrong_pointed *)
(*     | [H: context[@Algebra.bar _ (@Bar_pointed _ _)] |- _] => unfold Algebra.bar, Bar_pointed in H *)
(*     | [ |- context[@Algebra.bar _ (@Bar_pointed _ _)]] => unfold Algebra.bar, Bar_pointed *)
(*     | [H: context[@Algebra.eps _ (@Eps_pointed _ _)] |- _] => unfold Algebra.eps, Eps_pointed in H *)
(*     | [ |- context[@Algebra.eps _ (@Eps_pointed _ _)]] => unfold Algebra.eps, Eps_pointed *)
(*     | [H: context[@Algebra.oplus _ (@OPlus_pointed _ _)] |- _] => unfold Algebra.oplus, OPlus_pointed in H *)
(*     | [ |- context[@Algebra.oplus _ (@OPlus_pointed _ _)]] => unfold Algebra.oplus, OPlus_pointed *)
(*     end. *)

(* Global Program Instance refs_PreOrder: PreOrder (⊑S@{ModSem.t}). *)
(* Next Obligation. *)
(*   ii. upt. des_ifs. refl. *)
(* Qed. *)
(* Next Obligation. *)
(*   ii. upt. des_ifs. etrans; et. *)
(* Qed. *)

(* Global Program Instance refs_oplus: Proper ((⊑S@{ModSem.t}) ==> (⊑S) ==> (⊑S)) ((⊕)). *)
(* Next Obligation. *)
(*   ii. upt. des_ifs. rewrite H. rewrite H0. refl. *)
(* Qed. *)

(* Global Program Instance ModSem_RefStrongFacts: RefStrongFacts. *)
(* Next Obligation. *)
(*   { *)
(*     do 1 r. *)
(*     i. eapply ModSemPair.adequacy. upt. des_ifs. *)
(*     ss. rr in H. des; ss. econs; ss. *)
(*     { instantiate (1:=top2). ss. } *)
(*     2:{ instantiate (1:=top2). instantiate (1:=unit). ss. } *)
(*     ii; ss. *)
(*     hexploit Forall2_In_r; et. intro T; des. des_ifs. des; ss. subst. *)
(*     esplits; et. *)
(*     admit "ez". *)
(*   } *)
(*   (* { *) *)
(*   (*   ii. *) *)
(*   (*   assert(T: (ctx ⊕ x) ⊑S (ctx ⊕ y)). *) *)
(*   (*   { rewrite H. refl. } *) *)
(*   (*   upt. des_ifs; ss. *) *)
(*   (*   - eapply adequacy_global_itree2; et; ss. *) *)
(*   (*     unfold ModSem.initial_itr. *) *)
(*   (*     Local Opaque ModSem.prog. *) *)
(*   (*     rr in T. des; ss. admit "ez". *) *)
(*   (*   - admit "ez". *) *)
(*   (* } *) *)
(* Qed. *)
(* Next Obligation. *)
(*   ii. upt. des_ifs; ss. *)
(*   rename H into P. rename H0 into Q. rename H1 into R. *)
(*   symmetry in P. *)
(*   rr in P. rr in Q. rr in R. des; ss. *)
(*   rr. esplits; ss. *)
(*   2: { congruence. } *)
(*   clear P0 Q0 R0. *)
(*   eapply Forall2_impl. *)
(*   2: { eapply Forall2_trans; et. eapply Forall2_trans; et. } *)
(*   clear. *)
(*   i; ss. des. des_ifs. des; ss. clarify. esplits; ss. *)
(*   i. *)
(*   eapply simg_trans. *)
(*   { eapply eutt_simg; et. eapply PR4. } *)
(*   eapply simg_trans. *)
(*   2: { eapply eutt_simg; et. eapply PR2. } *)
(*   eapply PR3. *)
(* Qed. *)
(* Next Obligation. *)
(*   ii. upt. des_ifs. ss. *)
(*   rr in H. rr. des; ss. esplits; ss. *)
(*   eapply Forall2_apply_Forall2; et. clear. *)
(*   i. ss. des_ifs. des; ss. clarify. esplits; ss. *)
(*   i. unfold bar, ktree_Bar, bar, itree_Bar. *)
(*   eapply simg_interp; et. *)
(* Qed. *)

End ALGEBRA.
