Require Import Coqlib.
Require Export ZArith.
Require Export String.
Require Export Any.
Require Export Axioms.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Skeleton.
Require Import ModSem Mod ModSemFacts ModFacts.
Require Import Algebra.
Require Import SimModSem.
Require Import ImpPrelude.
Require Import HTactics.

Require Import IPM IPMAux.


Set Implicit Arguments.

Local Open Scope nat_scope.

Module SUCC.

  Definition succF : list val -> itree Es val :=
    fun varg =>
      n <- ((pargs [Tint] varg)?);;
      Ret (Vint (n + 1)).

  Definition succMS_ : ModSem._t :=
    {|
      ModSem.fnsems := [("succ", cfunU succF)];
      ModSem.initial_st := tt↑;
    |}.

  Definition succMS : ModSem.t := Algebra.just succMS_.

  Program Definition succM : Mod.t :=
    {|
      Mod.get_modsem := fun _ => succMS;
      Mod.sk := Sk.unit;
    |}.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.

  Lemma red_succF v: succF [Vint v] = Ret (Vint (v + 1)).
  Proof. unfold succF. grind. Qed.

End SUCC.

Module PUT.

  Definition putOnceF : list val -> itree Es val :=
    fun varg =>
      n <- ((pargs [Tint] varg)?);;
      x <- trigger (Syscall "print" ((Vint n)↑) top1);;
      Ret (Vint n).

  Definition putMS_ : ModSem._t :=
    {|
      ModSem.fnsems := [("putOnce", cfunU putOnceF)];
      ModSem.initial_st := tt↑;
    |}.

  Definition putMS : ModSem.t := Algebra.just putMS_.

  Program Definition putM : Mod.t :=
    {|
      Mod.get_modsem := fun _ => putMS;
      Mod.sk := Sk.unit;
    |}.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.

End PUT.

Module RPT0.

  Definition rptF : list val -> itree Es val :=
    fun varg =>
      '(fb, (n, x)) <- (pargs [Tptr; Tint; Tint] varg)?;;
      assume(intrange_64 n);;;
      if (Z_lt_le_dec n 1)
      then Ret (Vint x)
      else
        fn <- ((unname (Vptr (fst fb) (snd fb)))?);;
        v <- ccallU fn [Vint x];;
        ccallU "rpt" [Vptr (fst fb) (snd fb); Vint (n - 1); v].

  Definition rptMS_ : ModSem._t :=
    {|
      ModSem.fnsems := [("rpt", cfunU rptF)];
      ModSem.initial_st := tt↑;
    |}.

  Definition rptMS : ModSem.t := Algebra.just rptMS_.

  Program Definition rptM : Mod.t :=
    {|
      Mod.get_modsem := fun _ => rptMS;
      Mod.sk := Sk.unit;
    |}.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.

End RPT0.

Module RPT1.

  (* Expects (f: list val -> itree Es val), (x: itree Es val) *)
  Fixpoint fun_iter (f: Any.t -> itree Es Any.t) (n: nat) (x: itree Es Any.t): itree Es Any.t :=
    match n with
    | O => x
    | S n0 => vr <- x;; ` vr0: val <- (vr↓)?;; vr1 <- (f ([vr0]↑));; fun_iter f n0 (Ret vr1)
    end.

  Definition rptF (fn: string) (f: Any.t -> itree Es Any.t) : list val -> itree Es val :=
    fun varg =>
      '(fb, (n, x)) <- (pargs [Tptr; Tint; Tint] varg)?;;
      fn0 <- ((unname (Vptr (fst fb) (snd fb)))?);;
      if (String.eqb fn fn0)
      then
        assume(intrange_64 n);;;
        vret <- (fun_iter f (Z.to_nat n) (Ret (Vint x)↑));;
        vret0 <- (vret↓)?;;
        Ret vret0
      else
        triggerUB.

  Definition rptMS_ (fn: string) (f: Any.t -> itree Es Any.t): ModSem._t :=
    {|
      ModSem.fnsems := [("rpt", cfunU (rptF fn f))];
      ModSem.initial_st := tt↑;
    |}.

  Definition rptMS (fn: string) (f: Any.t -> itree Es Any.t): ModSem.t :=
    Algebra.just (rptMS_ fn f).

  Program Definition rptM fn f : Mod.t :=
    {|
      Mod.get_modsem := fun _ => rptMS fn f;
      Mod.sk := Sk.unit;
    |}.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.

End RPT1.

Module ONE.

  Definition oneMS_ (fn: string) (f: Any.t -> itree Es Any.t): ModSem._t :=
    {|
      ModSem.fnsems := [(fn, f)];
      ModSem.initial_st := tt↑;
    |}.

  Definition oneMS (fn: string) (f: Any.t -> itree Es Any.t): ModSem.t :=
    Algebra.just (oneMS_ fn f).

  Program Definition oneM fn f : Mod.t :=
    {|
      Mod.get_modsem := fun _ => oneMS fn f;
      Mod.sk := Sk.unit;
    |}.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.
  Next Obligation. ss. Qed.

End ONE.



Section PROOFSIM.

  Import ModSemPair.

  Lemma Z_to_nat_le_zero z: 0 = Z.to_nat z -> (z <= 0)%Z.
  Proof. intros. unfold Z.to_nat in H. des_ifs. pose proof (Pos2Nat.is_pos p). lia. Qed.

  Lemma Z_to_nat_ge_one z: forall n, S n = Z.to_nat z -> (z >= 1)%Z.
  Proof. intros. unfold Z.to_nat in H. des_ifs. lia. Qed.

  (* Definition cfunU_int {X} (body: X -> itree Es Z): Any.t -> itree Es Any.t := *)
  (*   fun '(varg) => varg <- varg↓?;; vret <- body varg;; Ret (Vint vret)↑. *)

  (* Definition simple_function (f: list val -> itree Es Z) := *)
  (*   forall vs, f vs = focus_right (f vs). *)

  (** Needs a way to handle paired states --- ex) focus_right *)
  (* Lemma simple_rpt_sim *)
  (*       (fn': string) (f': list val -> itree Es Z) *)
  (*       (SIMPLE: simple_function (f')) *)
  (*   : *)
  (*   ModSemPair.sim (RPT1.rptMS fn' (cfunU_int f')) (RPT0.rptMS ⊕ (ONE.oneMS fn' (cfunU_int f'))). *)
  (* Proof. *)
  (*   Local Opaque String.eqb. *)
  (*   ss. eapply mk. eapply (@top2_PreOrder unit). instantiate (1:= (fun _ '(src, tgt) => src = tgt)). *)
  (*   { i. ss. des; clarify. exists (focus_left (T:=Any.t) ∘ cfunU RPT0.rptF). split. *)
  (*     { left. f_equal. } *)
  (*     ii. subst y. ginit. *)
  (*     unfold_goal RPT1.rptF. unfold_goal RPT0.rptF. unfold_goal @cfunU. *)
  (*     unfold_goal @cfunU_int. *)
  (*     steps. *)
  (*     destruct p0. unfold unptr, unint, unr in *. des_ifs_safe. ss; clarify. *)
  (*     destruct (String.eqb_spec fn' s). *)
  (*     2:{ steps. } *)
  (*     clarify. *)
  (*     steps. *)
  (*     (* force_r. eexists; auto. steps. *) *)
  (*     rename z0 into v. *)
  (*     remember (Z.to_nat z) as n. *)
  (*     revert x z v _UNWRAPU _ASSUME Heqn mrs_tgt. induction n; intros. *)
  (*     { hexploit Z_to_nat_le_zero; eauto. intros. des_ifs. *)
  (*       2:{ lia. } *)
  (*       ss. steps. *)
  (*       (* unfold lift_rel. exists w; auto. *) *)
  (*     } *)
  (*     { hexploit Z_to_nat_ge_one; eauto. intros ZRANGE. des_ifs. clear l. *)
  (*       ss. *)
  (*       unfold ccallU. steps. *)
  (*       { right; left. instantiate (1:=focus_right (T:=Any.t) <*> cfunU_int f'). f_equal. } *)
  (*       unfold_goal @cfunU_int. steps. *)
  (*       guclo lbindC_spec. econs. *)
  (*       { guclo lflagC_spec. econs. gfinal. right. rewrite <- SIMPLE. eapply self_sim_itree. *)
  (*         all: auto. *)
  (*       } *)
  (*       (* rewrite ! SUCC.red_succF. steps. *) *)
  (*       i. rr in SIM. des. clear WLE. clarify. destruct w1. steps. *)
  (*       { left. instantiate (1:= focus_left (T:=Any.t) ∘ cfunU RPT0.rptF). auto. } *)
  (*       unfold_goal @cfunU. steps. unfold_goal RPT0.rptF. steps. *)
  (*       force_r. *)
  (*       { exfalso. apply _ASSUME0. clear - _ASSUME ZRANGE. unfold_intrange_64. *)
  (*         des_ifs. apply sumbool_to_bool_true in _ASSUME, H. *)
  (*         apply andb_true_intro. split; apply sumbool_to_bool_is_true; lia. *)
  (*       } *)
  (*       steps. *)
  (*       specialize (IHn ([Vptr (inr s) 0; Vint (z - 1); Vint (vret_tgt)]↑) (z - 1)%Z vret_tgt). *)
  (*       exploit IHn; auto. *)
  (*       { apply Any.upcast_downcast. } *)
  (*       { lia. } *)
  (*       clear IHn; intros IHn. des_ifs. *)
  (*       { steps. *)
  (*         match goal with *)
  (*         | [IHn: gpaco8 _ _ _ _ _ _ _ _ _ _ _ (?t1) |- *)
  (*              gpaco8 _ _ _ _ _ _ _ _ _ _ _ (?t2)] => *)
  (*             replace t2 with t1 *)
  (*         end. *)
  (*         guclo lflagC_spec. econs. eapply IHn. *)
  (*         all: auto. *)
  (*         f_equal. ired_eq_l. auto. *)
  (*       } *)
  (*       { steps. irw in IHn. *)
  (*         guclo guttC_spec. econs. *)
  (*         { guclo lflagC_spec. econs. eapply IHn. all: auto. } *)
  (*         - apply Reflexive_eqit_eq. *)
  (*         - ired_eq_r. *)
  (*           apply eqit_bind. apply Reflexive_eqit_eq. ii. *)
  (*           apply eqit_bind. apply Reflexive_eqit_eq. ii. *)
  (*           ired_eq_l. apply eqit_Tau_l. ired_eq_l. ired_eq_r. *)
  (*           apply Reflexive_eqit_eq. *)
  (*       } *)
  (*     } *)
  (*   } *)
  (*   { ss. exists tt. auto. } *)
  (* Qed. *)

  Lemma succ_rpt_sim:
    ModSemPair.sim (RPT1.rptMS "succ" (cfunU SUCC.succF)) (RPT0.rptMS ⊕ SUCC.succMS).
  Proof.
    Local Opaque String.eqb.
    ss. eapply mk. eapply Nat.le_preorder. instantiate (1:= fun _ _ => True).
    { i. ss. des; clarify. exists (focus_left (T:=Any.t) ∘ cfunU RPT0.rptF). split.
      { left. f_equal. }
      unfold RPT1.rptF. unfold RPT0.rptF at 2. unfold cfunU at 3 4.
      unfold sim_fsem. ii. subst y.
      ginit.
      unfold cfunU at 5. steps.
      destruct p0. unfold unptr, unint, unr in *. des_ifs_safe. ss; clarify.
      destruct (String.eqb_spec "succ" s).
      2:{ steps. }
      clarify.
      steps.
      (* force_r. eexists; auto. steps. *)
      rename z0 into v.
      remember (Z.to_nat z) as n.
      revert x z v _UNWRAPU _ASSUME Heqn. induction n; intros.
      { hexploit Z_to_nat_le_zero; eauto. intros. des_ifs.
        2:{ lia. }
        ss. steps.  unfold lift_rel. exists w; auto.
      }
      { hexploit Z_to_nat_ge_one; eauto. intros ZRANGE. des_ifs. clear l.
        ss.
        unfold ccallU. steps.
        { right; left. instantiate (1:=focus_right (T:=Any.t) ∘ cfunU SUCC.succF). f_equal. }
        unfold cfunU at 5. steps.
        rewrite ! SUCC.red_succF. steps.
        { left. instantiate (1:= focus_left (T:=Any.t) ∘ cfunU RPT0.rptF). auto. }
        unfold cfunU at 5. steps. unfold RPT0.rptF at 3. steps.
        force_r.
        { exfalso. apply _ASSUME0. clear - _ASSUME ZRANGE. unfold_intrange_64.
          des_ifs. apply sumbool_to_bool_true in _ASSUME, H.
          apply andb_true_intro. split; apply sumbool_to_bool_is_true; lia.
        }
        steps.
        specialize (IHn ([Vptr (inr "succ") 0; Vint (z - 1); Vint (v +1)]↑) (z - 1)%Z (v + 1)%Z).
        hexploit IHn; auto.
        { apply Any.upcast_downcast. }
        { lia. }
        clear IHn; intros IHn. des_ifs.
        { steps.
          match goal with
          | [IHn: gpaco8 _ _ _ _ _ _ _ _ _ _ _ (?t1) |-
               gpaco8 _ _ _ _ _ _ _ _ _ _ _ (?t2)] =>
              replace t2 with t1
          end.
          guclo lflagC_spec. econs. eapply IHn.
          all: auto.
          f_equal. ired_eq_l. auto.
        }
        { steps. irw in IHn.
          guclo guttC_spec. econs.
          { guclo lflagC_spec. econs. eapply IHn. all: auto. }
          - apply Reflexive_eqit_eq.
          - ired_eq_r.
            apply eqit_bind. apply Reflexive_eqit_eq. ii.
            apply eqit_bind. apply Reflexive_eqit_eq. ii.
            ired_eq_l. apply eqit_Tau_l. ired_eq_l. ired_eq_r.
            apply Reflexive_eqit_eq.
        }
      }
    }
    { ss. exists O. auto. }
  Qed.

  Lemma putOnce_rpt_sim:
    ModSemPair.sim (RPT1.rptMS "putOnce" (cfunU PUT.putOnceF)) (RPT0.rptMS ⊕ PUT.putMS).
  Proof.
    Local Opaque String.eqb.
    ss. eapply mk. eapply Nat.le_preorder. instantiate (1:= fun _ _ => True).
    { i. ss. des; clarify. exists (focus_left (T:=Any.t) ∘ cfunU RPT0.rptF). split.
      { left. f_equal. }
      unfold RPT1.rptF. unfold RPT0.rptF at 2. unfold cfunU at 3 4.
      unfold sim_fsem. ii. subst y.
      ginit.
      unfold cfunU at 5. steps.
      destruct p0. unfold unptr, unint, unr in *. des_ifs_safe. ss; clarify.
      destruct (String.eqb_spec "putOnce" s).
      2:{ steps. }
      clarify.
      steps.
      (* force_r. eexists; auto. steps. *)
      rename z0 into v.
      remember (Z.to_nat z) as n.
      revert x z v _UNWRAPU _ASSUME Heqn. induction n; intros.
      { hexploit Z_to_nat_le_zero; eauto. intros. des_ifs.
        2:{ lia. }
        ss. steps.  unfold lift_rel. exists w; auto.
      }
      { hexploit Z_to_nat_ge_one; eauto. intros ZRANGE. des_ifs. clear l.
        ss.
        unfold ccallU. steps.
        { right; left. instantiate (1:=focus_right (T:=Any.t) ∘ cfunU PUT.putOnceF). f_equal. }
        unfold cfunU at 5. steps.
        unfold PUT.putOnceF at 3 5. steps.
        { left. instantiate (1:= focus_left (T:=Any.t) ∘ cfunU RPT0.rptF). auto. }
        unfold cfunU at 5. steps. unfold RPT0.rptF at 3. steps.
        force_r.
        { exfalso. apply _ASSUME0. clear - _ASSUME ZRANGE. unfold_intrange_64.
          des_ifs. apply sumbool_to_bool_true in _ASSUME, H.
          apply andb_true_intro. split; apply sumbool_to_bool_is_true; lia.
        }
        steps.
        specialize (IHn ([Vptr (inr "putOnce") 0; Vint (z - 1); Vint (v)]↑) (z - 1)%Z (v)%Z).
        hexploit IHn; auto.
        { apply Any.upcast_downcast. }
        { lia. }
        clear IHn; intros IHn. des_ifs.
        { steps.
          match goal with
          | [IHn: gpaco8 _ _ _ _ _ _ _ _ _ _ _ (?t1) |-
               gpaco8 _ _ _ _ _ _ _ _ _ _ _ (?t2)] =>
              replace t2 with t1
          end.
          guclo lflagC_spec. econs. eapply IHn.
          all: auto.
          f_equal. ired_eq_l. auto.
        }
        { steps. irw in IHn.
          guclo guttC_spec. econs.
          { guclo lflagC_spec. econs. eapply IHn. all: auto. }
          - apply Reflexive_eqit_eq.
          - ired_eq_r.
            apply eqit_bind. apply Reflexive_eqit_eq. ii.
            apply eqit_bind. apply Reflexive_eqit_eq. ii.
            ired_eq_l. apply eqit_Tau_l. ired_eq_l. ired_eq_r.
            apply Reflexive_eqit_eq.
        }
      }
    }
    { ss. exists O. auto. }
  Qed.

  Theorem succ_rpt_ref: (RPT0.rptM ⊕ SUCC.succM) ⊑ (RPT1.rptM "succ" (cfunU SUCC.succF)).
  Proof.
    eapply LSimMod. ss. ss. i. eapply ModSemPair.adequacy. apply succ_rpt_sim.
  Qed.

  Theorem putOnce_rpt_ref: (RPT0.rptM ⊕ PUT.putM) ⊑ (RPT1.rptM "putOnce" (cfunU PUT.putOnceF)).
  Proof.
    eapply LSimMod. ss. ss. i. eapply ModSemPair.adequacy. apply putOnce_rpt_sim.
  Qed.

End PROOFSIM.

Section PROOF.

  Lemma own_persistent (M: MRAS.t) (m: M)
    :
    (Own m) -∗ (□ Own ( | m | )).
  Proof.
    rr. econs. ii. rr. split.
    { rr. auto. }
    rr. rr in H. des. exists ( | ctx | ). rewrite <- bar_oplus. rewrite H. auto.
  Qed.

  Lemma ownm_persistent
        (m: Mod.t)
    :
    (OwnM m) -∗ (□ OwnM ( | m | )).
  Proof. eapply own_persistent. Qed.

  Lemma rpt0_core
    :
    RPT0.rptM ≡ | RPT0.rptM |.
  Proof.
    rr. ss. split; auto. ii.
    unfold bar, ktree_Bar.
    unfold cfunU, RPT0.rptF.
    unfold equiv, Mod.equiv. splits; ss. ii.
    unfold equiv, ModSem.equiv, RPT0.rptMS, RPT0.rptMS_. ss.
    unfold equiv. ss. split; auto. econs; auto.
    split; auto.
    ii.
    unfold bar, ktree_Bar.
    unfold cfunU, RPT0.rptF.
    ired_eq_r. grind. apply eutt_eq_bind; [refl | ii].
    ired_eq_r. grind. apply eutt_eq_bind; [refl | ii].
    grind. ired_eq_r. grind. apply eutt_eq_bind; [refl | ii].
    grind. des_ifs.
    { ired_eq_r. grind. refl. }
    { grind. ired_eq_r. apply eutt_eq_bind; [refl | ii].
      unfold ccallU.
      grind. ired_eq_r. apply eutt_eq_bind; [refl | ii].
      grind. symmetry. etrans. apply tau_eutt.
      grind. symmetry. ired_eq_r. grind. apply eutt_eq_bind; [refl | ii].
      grind. ired_eq_r. apply eutt_eq_bind; [refl | ii].
      grind. symmetry. etrans. apply tau_eutt.
      grind. symmetry. ired_eq_r. grind. apply eutt_eq_bind; [refl | ii].
      grind. ired_eq_r. refl.
    }
    { grind. ired_eq_r. apply eutt_eq_bind; [refl | ii].
      unfold ccallU.
      grind. ired_eq_r. apply eutt_eq_bind; [refl | ii].
      grind. symmetry. etrans. apply tau_eutt.
      grind. symmetry. ired_eq_r. grind. apply eutt_eq_bind; [refl | ii].
      grind. ired_eq_r. apply eutt_eq_bind; [refl | ii].
      grind. symmetry. etrans. apply tau_eutt.
      grind. symmetry. ired_eq_r. grind. apply eutt_eq_bind; [refl | ii].
      grind. ired_eq_r. refl.
    }
  Qed.

  Lemma rpt0_core_mras
    :
    @equiv (@MRAS.car (MRA_to_MRAS (@Mod_MRA _)))
           (@MRAS.equiv (MRA_to_MRAS (@Mod_MRA _)))
           RPT0.rptM ( | RPT0.rptM | ).
  Proof.
    rr. unfold ref_both. splits.
    rewrite <- rpt0_core. auto.
    rewrite <- rpt0_core. auto.
    rewrite <- rpt0_core. auto.
    rewrite <- rpt0_core. auto.
  Qed.

  Lemma rpt0_persistent0
    :
    OwnM ( | RPT0.rptM | ) -∗ OwnM RPT0.rptM.
  Proof.
    econs. ii. rr in H. des. rr. exists ctx. etrans. 2: eapply H.
    eapply oplus_Proper; auto. eapply rpt0_core_mras.
  Qed.

  Lemma rpt0_persistent
    :
    (OwnM RPT0.rptM) -∗ (□ (OwnM RPT0.rptM)).
  Proof.
    iIntros "H". iPoseProof (ownm_persistent with "H") as "H".
    iStopProof. apply bi.intuitionistically_mono'. apply rpt0_persistent0.
  Qed.

  Global Program Instance Persistent_rpt0: Persistent (OwnM RPT0.rptM).
  Next Obligation.
  Proof.
    iIntros "H". iPoseProof (rpt0_persistent with "H") as "H". auto.
  Qed.

  Lemma succ_rpt_ref_iprop:
    OwnM RPT0.rptM ∗ OwnM SUCC.succM ⊢ |==> OwnM (RPT1.rptM "succ" (cfunU SUCC.succF)).
  Proof.
    iIntros "[RPT0 SUCC]". iPoseProof (own_sep with "[SUCC RPT0]") as "OWN". iFrame.
    iStopProof. apply IPM.adequacy. apply succ_rpt_ref.
  Qed.

  Lemma putOnce_rpt_ref_iprop:
    OwnM RPT0.rptM ∗ OwnM PUT.putM ⊢ |==> OwnM (RPT1.rptM "putOnce" (cfunU PUT.putOnceF)).
  Proof.
    iIntros "[RPT0 PUT]". iPoseProof (own_sep with "[PUT RPT0]") as "OWN". iFrame.
    iStopProof. apply IPM.adequacy. apply putOnce_rpt_ref.
  Qed.

  Theorem rpts_ref_iprop:
    OwnM RPT0.rptM ∗ OwnM SUCC.succM ∗ OwnM PUT.putM
      ⊢
      |==> ((OwnM (RPT1.rptM "succ" (cfunU SUCC.succF)))
              ∗ (OwnM (RPT1.rptM "putOnce" (cfunU PUT.putOnceF)))).
  Proof.
    iIntros "[#RPT0 [SUCC PUT]]".
    iPoseProof (succ_rpt_ref_iprop with "[SUCC]") as "SUCCREF". iFrame. auto.
    iPoseProof (putOnce_rpt_ref_iprop with "[PUT]") as "PUTREF". iFrame. auto.
    iMod "SUCCREF". iMod "PUTREF". iModIntro. iFrame.
  Qed.

  Theorem rpts_ref:
    (RPT0.rptM ⊕ SUCC.succM ⊕ PUT.putM)
      ⊑
      (RPT1.rptM "succ" (cfunU SUCC.succF)) ⊕ (RPT1.rptM "putOnce" (cfunU PUT.putOnceF)).
  Proof.
    pose proof rpts_ref_iprop. do 2 setoid_rewrite <- own_sep in H.
    eapply IPM.adequacy in H. rewrite oplus_assoc in H. eapply H.
  Qed.

End PROOF.
