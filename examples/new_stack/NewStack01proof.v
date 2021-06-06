Require Import NewStack0 NewStack1 HoareDef SimModSem.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
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
Require Import TODOYJ.
Require Import HTactics Logic IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section AUX.

  Context `{Σ: GRA.t}.

  Lemma APCK_start_clo
        (at_most: Ord.t) (n1: Ord.t)
        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt

        (ATMOST: (at_most < kappa)%ord)
        (FUEL: (n1 + 5 < n0)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                       (mr_src0, mp_src0, fr_src0,
                       (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK at_most))) >>= k_src)
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
              (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt APCK)) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    unfold APCK. steps. force_l.
    exists at_most. ired_l.  _step; [by eauto with ord_step|]. steps; [by eauto with ord_step|].
    unfold guarantee. ired_both. force_l. esplits; et.
    ired_both. _step; [by eauto with ord_step|]. steps; [by eauto with ord_step|]. ss.
    guclo lordC_spec. econs; et. rewrite OrdArith.add_O_r. refl.
  Qed.

  Lemma APCK_step_clo
        (fn: gname) (next: Ord.t) (n1: Ord.t)

        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (at_most: Ord.t)
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt

        (FUEL: (n1 + 11 < n0)%ord)
        (ftsp: ftspec unit unit)
        (FIND: alist_find fn stb = Some (KModSem.disclose ftsp))
        (NEXT: (next < at_most)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                      (mr_src0, mp_src0, fr_src0,
                       (HoareCall true o (KModSem.disclose ftsp) fn (inl tt));;;
                                 tau;; tau;; (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK next)))
                                               >>= k_src)
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
             (mr_src0, mp_src0, fr_src0, (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK at_most)))
                                           >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    rewrite unfold_APCK. steps. force_l. exists false. ired_both.
    _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l. esplits; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    force_l. esplits; et.
    ired_both; _step; [by eauto with ord_step|].
    steps; [by eauto with ord_step|].
    rewrite FIND. ired_both. rewrite Any.upcast_downcast. ired_both.
    guclo lordC_spec. econs; et. { rewrite OrdArith.add_O_r. refl. }
    match goal with
    | [SIM: gpaco6 _ _ _ _ _ _ _ _ ?i0 _ |- gpaco6 _ _ _ _ _ _ _ _ ?i1 _] =>
      replace i1 with i0; auto
    end.
    f_equal. grind. ired_both. grind. ired_both. grind.
  Qed.

  Lemma APCK_stop_clo
        (n1: Ord.t)

        (o: ord)
        r rg (n0: Ord.t) mr_src0 mp_src0 fr_src0
        mrs_tgt frs_tgt k_src
        (at_most: Ord.t)
        (wf: (Σ * Any.t) * (Σ * Any.t) -> Prop)
        (eqr: Σ * Any.t * Σ -> Σ * Any.t * Σ -> Any.t -> Any.t -> Prop)
        stb itr_tgt

        (FUEL: (n1 + 2 < n0)%ord)

        (POST: gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) rg rg _ _ eqr n1
                      (mr_src0, mp_src0, fr_src0, k_src ())
                      ((mrs_tgt, frs_tgt),
                       itr_tgt))
    :
      gpaco6 (_sim_itree wf) (cpn6 (_sim_itree wf)) r rg _ _ eqr n0
              (mr_src0, mp_src0, fr_src0,
              (interp_hCallE_tgt stb o (KModSem.transl_itr_tgt (_APCK at_most))) >>= k_src)
             ((mrs_tgt, frs_tgt),
              itr_tgt).
  Proof.
    rewrite unfold_APCK. steps. force_l. exists true.
    ired_both; _step; [by eauto with ord_step|].
    ired_both; _step; [by eauto with ord_step|].
    steps.
    guclo lordC_spec. econs; et. { rewrite OrdArith.add_O_r. refl. }
  Qed.

End AUX.

Ltac kstart _at_most :=
  eapply (APCK_start_clo) with (at_most := _at_most);
  [eauto with ord_kappa|
   (try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
  ]
.

Ltac kstep _fn :=
  eapply (@APCK_step_clo _ _fn);
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|
   (try by (stb_tac; refl))|
   (eapply OrdArith.lt_from_nat; eapply Nat.lt_succ_diag_r)|
  ].

Ltac kcatch :=
  match goal with
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn _) >>= _)) ] =>
    kstep fn
  end.

Ltac kstop :=
  eapply APCK_stop_clo;
  [(try by (eapply Ord.eq_lt_lt; [(symmetry; eapply OrdArith.add_from_nat)|(eapply OrdArith.lt_from_nat; eapply Nat.lt_add_lt_sub_r; eapply Nat.lt_succ_diag_r)]))|].




Section AUX.

  Context `{Σ: GRA.t}.

  Lemma forall_sep_commute
        X
        (P Q: X -> iProp')
    :
      (∀ x, P x ** Q x) -∗ (∀ x, P x) ** (∀ x, Q x)
  .
  Proof.
    uipropall. ii. rr in H. uipropall.
    hexploit (@ClassicalChoice.choice X (Σ * Σ) (fun x '(a, b) => P x a /\ Q x b)).
    { intro x. spc H. uipropall. des. subst. exists (a, b). et. }
    i. des.
    ...?
  Qed.

  Lemma forall_split
        X (xcond: X -> bool)
        (P: X -> iProp')
    :
      (∀ x, P x) -∗ (∀ x, ⌜xcond x⌝ -* P x) ** (∀ x, ⌜~xcond x⌝ -* P x)
  .
  Proof.
  Qed.

End AUX.




Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  (*** TODO: remove redundancy with Stack1.v ***)
  Fixpoint is_list (ll: val) (xs: list val): iProp :=
    match xs with
    | [] => (⌜ll = Vnullptr⌝: iProp)%I
    | xhd :: xtl =>
      (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ** (OwnM ((lhd,0%Z) |-> [xhd; ltl]))
                             ** is_list ltl xtl: iProp)%I
    end
  .

  Let wf: W -> Prop :=
    @mk_wf _ unit
           (fun _ _stk_mgr0 _ =>
              (∃ stk_mgr0, (⌜<<CAST: _stk_mgr0 = stk_mgr0↑>>⌝) ∧
                           (∀ handle stk, (⌜<<ABS: stk_mgr0 handle = Some stk>>⌝) -*
                                    (∃ hd, OwnM ((handle, 0%Z) |-> [hd]) ** is_list hd (map Vint stk))))%I)
           (fun _ _ _ => ⌜True⌝%I)
  .

  (*** TODO: remove redundancy with Mem0OpenProof ***)
  Definition __hide_mark A (a : A) : A := a.
  Lemma intro_hide_mark: forall A (a: A), a = __hide_mark a. refl. Qed.

  Ltac hide_k := 
    match goal with
    | [ |- (gpaco6 _ _ _ _ _ _ _ _ (_, ?isrc >>= ?ksrc) (_, ?itgt >>= ?ktgt)) ] =>
      erewrite intro_hide_mark with (a:=ksrc);
      erewrite intro_hide_mark with (a:=ktgt);
      let name0 := fresh "__KSRC__" in set (__hide_mark ksrc) as name0; move name0 at top;
      let name0 := fresh "__KTGT__" in set (__hide_mark ktgt) as name0; move name0 at top
    end.

  Ltac unhide_k :=
    do 2 match goal with
    | [ H := __hide_mark _ |- _ ] => subst H
    end;
    rewrite <- ! intro_hide_mark
  .

  Ltac mRename A B :=
    match goal with
    | [H: current_iPropL _ ?iprops |- _ ] =>
      match iprops with
      | context[(A, ?x)] => mAssert x with A as B; [iApply A|]
      end
    end.
  Ltac mRefresh := on_current ltac:(fun H => move H at bottom).

  (*** TODO: move to Mem1.v ***)
  Lemma points_to_disj
        ptr x0 x1
    :
      (OwnM (ptr |-> [x0]) -∗ OwnM (ptr |-> [x1]) -* ⌜False⌝)
  .
  Proof.
    destruct ptr as [blk ofs].
    iIntros "A B". iCombine "A B" as "A". iOwnWf "A" as WF0.
    unfold points_to in WF0. rewrite ! unfold_points_to in *. repeat (ur in WF0); ss.
    specialize (WF0 blk ofs). des_ifs; bsimpl; des; des_sumbool; zsimpl; ss; try lia.
  Qed.

  Variable global_stb: list (string * fspec).
  Hypothesis STBINCL: stb_incl (DebugStb ++ StackStb ++ MemStb) global_stb.

  Theorem sim_modsem: ModSemPair.sim (NewStack1.StackSem global_stb) NewStack0.StackSem.
  Proof.
    econstructor 1 with (wf:=wf); ss; et; swap 2 3.
    { econs; ss.
      - eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iExists _. iSplit; ss. iIntros; ss.
      - eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iPureIntro. ss.
    }
    econs; ss.
    { unfold newF. init. harg. destruct varg_src.
      { ss. des_ifs; mDesAll; ss. }
      destruct x; mDesAll; ss. des; subst.
      unfold new_body, ccall. steps. rewrite Any.upcast_downcast in *; clarify. steps. kstart 1.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall _ (Some _) _ with "A"; ss; et.
      { iModIntro. iSplitL; ss; et. iPureIntro. esplits; et. instantiate (1:=1%nat). ss. }
      { ss. }
      steps. mDesAll. des; clarify. rewrite Any.upcast_downcast in *. clarify. kstop. steps.
      rename a3 into handle. force_l. exists handle. steps. rewrite Any.upcast_downcast. steps.
      rename a2 into stk_mgr0. destruct (stk_mgr0 handle) eqn:T.
      { mAssertPure False; ss. iSpecialize ("A" $! _ _ T). iDestruct "A" as (x) "[A B]".
        iApply (points_to_disj with "A A1"); et.
      }
      force_l; ss. steps.

      hret _; ss.
      { iModIntro. iSplitL; ss. iExists _. iSplit; ss. iIntros. des_ifs.
        - des; clarify. et.
        - iClear "A1". des; clarify. iSpecialize ("A" $! _ _ H0). et.
      }
    }
    econs; ss.
    { unfold popF. init. harg. destruct varg_src.
      { ss. des_ifs; mDesAll; ss. }
      destruct x; mDesAll; ss. des; subst.
      unfold pop_body, ccall. steps. rewrite Any.upcast_downcast in *; clarify. steps. kstart 7.

      hide_k. destruct v; ss. des_ifs.
      rename n into handle. rename a0 into stk_mgr0. rename l into stk. rename _UNWRAPU0 into T.
      mAssert _ with "".
      { Ltac mRamify A P B :=
          match goal with
          | [H: current_iPropL _ ?iprops |- _ ] =>
            match iprops with
            | context[(A, ?x)] => mAssert (P ** (P -* x)) with A as B
            end
          end.
        mRamify "A" (((∃ hd : val, OwnM ((handle, 0%Z) |-> [hd]) ** is_list hd (map Vint stk)))%I) "B".
        {

        match goal with
        instantiate (1:=((∀ (handle : nat) (stk : list Z),
             ⌜<<ABS: stk_mgr0 handle = Some stk >>⌝ -*
             (∃ hd : val, OwnM ((handle, 0%Z) |-> [hd]) ** is_list hd (map Vint stk)))%I)).

      mSpcUniv "A" with handle. mSpcUniv "A" with stk.
      mAssert _ with "". { instantiate (1:=(⌜_⌝%I)). iPureIntro. exact T. } mSpcWand "A" with "A1".
      mDesAll. rename a0 into hd. unhide_k.

      kcatch. { eapply STBINCL. stb_tac; ss. } hcall _ (Some _) _ with "A"; ss; et.
      { iModIntro. iSplitL; ss; et. iPureIntro. esplits; et. instantiate (1:=1%nat). ss. }
      { ss. }
      steps. mDesAll. des; clarify. rewrite Any.upcast_downcast in *. clarify. kstop. steps.
      rename a3 into handle. force_l. exists handle. steps. rewrite Any.upcast_downcast. steps.
      rename a2 into stk_mgr0. destruct (stk_mgr0 handle) eqn:T.
      { mAssertPure False; ss. iSpecialize ("A" $! _ _ T). iDestruct "A" as (x) "[A B]".
        iApply (points_to_disj with "A A1"); et.
      }
      force_l; ss. steps.

      hret _; ss.
      { iModIntro. iSplitL; ss. iExists _. iSplit; ss. iIntros. des_ifs.
        - des; clarify. et.
        - iClear "A1". des; clarify. iSpecialize ("A" $! _ _ H0). et.
      }
    }
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Theorem correct: ModPair.sim (MemClient1.Client (fun _ => (UnknownStb ++ ClientStb ++ MemStb)))
                               MemClient0.Client.
  Proof.
    econs; ss.
    { ii. eapply adequacy_lift. eapply sim_modsem. }
    ii; ss. repeat (econs; ss).
  Qed.

End SIMMOD.
