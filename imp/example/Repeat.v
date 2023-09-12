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

Require Import IPM IPMAux WrapMod WrapModSem.


Set Implicit Arguments.

Local Open Scope nat_scope.

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
  Next Obligation. ss. refl. Qed.

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
  Next Obligation. ss. refl. Qed.

End RPT1.


Definition cast_val {X} (body: X -> itree Es Z): X -> itree Es val :=
  fun '(varg) => vret <- body varg;; Ret (Vint vret).

Definition cfunU_int {X} (body: X -> itree Es Z): Any.t -> itree Es Any.t :=
  cfunU (cast_val body).

Module ONE.

  Definition oneMS_ (fn: string) (f: list val -> itree Es Z): ModSem._t :=
    {|
      ModSem.fnsems := [(fn, cfunU_int f)];
      ModSem.initial_st := tt↑;
    |}.

  Definition oneMS (fn: string) (f: list val -> itree Es Z): ModSem.t :=
    Algebra.just (oneMS_ fn f).

  Program Definition oneM fn f : Mod.t :=
    {|
      Mod.get_modsem := fun _ => oneMS fn f;
      Mod.sk := Sk.unit;
    |}.
  Next Obligation. ss. Qed.
  Next Obligation. ss. refl. Qed.

End ONE.

Module SUCC.

  Definition succF : list val -> itree Es Z :=
    fun varg =>
      n <- ((pargs [Tint] varg)?);;
      Ret (n + 1)%Z.

  Definition succM : Mod.t := ONE.oneM "succ" succF.

End SUCC.

Module PUT.

  Definition putOnceF : list val -> itree Es Z :=
    fun varg =>
      n <- ((pargs [Tint] varg)?);;
      x <- trigger (SyscallOut "print" ((Vint n)↑) top1);;
      Ret (n).

  Definition putM : Mod.t := ONE.oneM "putOnce" putOnceF.

End PUT.


Section PROOFSIM.

  Import ModSemPair.

  Lemma Z_to_nat_le_zero z: 0 = Z.to_nat z -> (z <= 0)%Z.
  Proof. intros. unfold Z.to_nat in H. des_ifs. pose proof (Pos2Nat.is_pos p). lia. Qed.

  Lemma Z_to_nat_ge_one z: forall n, S n = Z.to_nat z -> (z >= 1)%Z.
  Proof. intros. unfold Z.to_nat in H. des_ifs. lia. Qed.

  Lemma one_rpt_sim
        (fn': string) (f': list val -> itree Es Z)
    :
    ModSemPair.sim (RPT1.rptMS fn' (cfunU_int f')) (RPT0.rptMS ⊕ (ONE.oneMS fn' f')).
  Proof.
    Local Opaque String.eqb.
    ss. eapply mk. eapply (@top2_PreOrder unit). instantiate (1:= (fun _ '(src, tgt) => exists tgt_l, tgt = Any.pair tgt_l src)).
    { i. ss. des; clarify. exists (focus_left (T:=Any.t) ∘ cfunU RPT0.rptF). split.
      { left. f_equal. }
      ii. subst y. ginit.
      unfold_goal RPT1.rptF. unfold_goal RPT0.rptF. unfold_goal @cfunU.
      unfold_goal @cfunU_int. unfold_goal @cast_val.
      steps.
      destruct p0. unfold unptr, unint, unr in *. des_ifs_safe. ss; clarify.
      destruct (String.eqb_spec fn' s).
      2:{ steps. }
      clarify.
      steps.
      (* force_r. eexists; auto. steps. *)
      rename z0 into v.
      des; clarify.
      remember (Z.to_nat z) as n.
      revert x z v _UNWRAPU _ASSUME Heqn mrs_src tgt_l. induction n; intros.
      { hexploit Z_to_nat_le_zero; eauto. intros. des_ifs.
        2:{ lia. }
        ss. steps.
        unfold lift_rel. exists w; splits; eauto.
      }
      { hexploit Z_to_nat_ge_one; eauto. intros ZRANGE. des_ifs. clear l.
        ss.
        unfold ccallU. steps.
        { right; left. instantiate (1:=focus_right (T:=Any.t) <*> cfunU_int f'). f_equal. }
        unfold_goal @cfunU_int. unfold_goal @cfunU. unfold_goal @cast_val. steps.
        guclo lbindC_spec. econs.
        { guclo lflagC_spec. econs. gfinal. right.
          eapply sim_itree_fsubset. 2: eapply sim_itree_tgtr. ss. eapply self_sim_itree.
          all: eauto.
          i. ss. split; ii.
          - des. clarify. eauto.
          - des. clarify. eauto.
        }
        i. rr in SIM. des. clear WLE. clarify. destruct w1. steps.
        { left. instantiate (1:= focus_left (T:=Any.t) ∘ cfunU RPT0.rptF). auto. }
        unfold_goal @cfunU. steps. unfold_goal RPT0.rptF. steps.
        force_r.
        { exfalso. apply _ASSUME0. clear - _ASSUME ZRANGE. unfold_intrange_64.
          des_ifs. apply sumbool_to_bool_true in _ASSUME, H.
          apply andb_true_intro. split; apply sumbool_to_bool_is_true; lia.
        }
        steps.
        specialize (IHn ([Vptr (inr s) 0; Vint (z - 1); Vint (vret_tgt)]↑) (z - 1)%Z vret_tgt).
        exploit IHn; auto.
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
    { ss. exists tt. eauto. }
  Qed.

  Theorem one_rpt_ref fn f:
    (RPT0.rptM ⊕ (ONE.oneM fn f)) ⊑ (RPT1.rptM fn (cfunU_int f)).
  Proof.
    eapply LSimMod. ss. ss. i. eapply ModSemPair.adequacy. apply one_rpt_sim.
  Qed.

  Theorem succ_rpt_ref:
    (RPT0.rptM ⊕ SUCC.succM) ⊑ (RPT1.rptM "succ" (cfunU_int SUCC.succF)).
  Proof. eapply one_rpt_ref. Qed.

  Theorem putOnce_rpt_ref:
    (RPT0.rptM ⊕ PUT.putM) ⊑ (RPT1.rptM "putOnce" (cfunU_int PUT.putOnceF)).
  Proof. eapply one_rpt_ref. Qed.

End PROOFSIM.

Section PROOF.

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

  (*** YJ: equiv_relaxed should not appear to the user. equiv should be sufficient. ***)
  (* Lemma rpt0_core_mras *)
  (*   : *)
  (*   @equiv (@MRAS.car (MRA_to_MRAS (@Mod_MRA _))) *)
  (*          (@MRAS.equiv (MRA_to_MRAS (@Mod_MRA _))) *)
  (*          RPT0.rptM ( | RPT0.rptM | ). *)
  (* Proof. *)
  (*   rr. unfold ref_both. splits. *)
  (*   rewrite <- rpt0_core. auto. *)
  (*   rewrite <- rpt0_core. auto. *)
  (*   rewrite <- rpt0_core. auto. *)
  (*   rewrite <- rpt0_core. auto. *)
  (* Qed. *)

  Lemma rpt0_persistent0
    :
    OwnM ( | RPT0.rptM | ) -∗ OwnM RPT0.rptM.
  Proof.
    econs. ii. rr in H. des. rr. exists ctx. etrans. 2: eapply H.
    eapply oplus_Proper; auto. rewrite <- rpt0_core. refl.
  Qed.

  Lemma rpt0_persistent
    :
    (OwnM RPT0.rptM) -∗ (□ (OwnM RPT0.rptM)).
  Proof.
    iIntros "H". iPoseProof (OwnM_persistent with "H") as "[_ #B]". iModIntro.
    iApply rpt0_persistent0; ss.
  Qed.

  Global Program Instance Persistent_rpt0: Persistent (OwnM RPT0.rptM).
  Next Obligation.
  Proof.
    iIntros "H". iPoseProof (rpt0_persistent with "H") as "H". auto.
  Qed.

  Lemma rpt0_spec:
    OwnM (RPT0.rptM) ⊢ □ (∀ fn f, OwnM (ONE.oneM fn f) ==∗ OwnM (RPT1.rptM fn (cfunU_int f))).
  Proof.
    iIntros "#RPT0". iModIntro. iIntros (fn f) "ONE".
    iPoseProof (own_sep with "[ONE RPT0]") as "OWN". iSplitL "RPT0". auto. iApply "ONE".
    iClear "RPT0".
    iStopProof. apply IPM.adequacy. apply one_rpt_ref.
  Qed.

  (** Coq complains that type is wrong. *)
  (* Definition REF : mProp := *)
  (*   ∀ (fn: string) (f: list val -> itree Es Z), *)
  (*     OwnM (ONE.oneM fn f) ==∗ OwnM (RPT1.rptM fn (cfunU_int f)). *)

  Theorem rpts_ref_iprop:
    OwnM RPT0.rptM ∗ OwnM SUCC.succM ∗ OwnM PUT.putM
      ⊢
      |==> ((OwnM (RPT1.rptM "succ" (cfunU_int SUCC.succF)))
              ∗ (OwnM (RPT1.rptM "putOnce" (cfunU_int PUT.putOnceF)))).
  Proof.
    iIntros "[#RPT0 [SUCC PUT]]".
    iPoseProof (rpt0_spec with "RPT0") as "#RPT0_SPEC".
    iPoseProof ("RPT0_SPEC" with "SUCC") as "SUCCREF".
    iPoseProof ("RPT0_SPEC" with "PUT") as "PUTREF".
    iMod "SUCCREF". iMod "PUTREF". iModIntro. iFrame.
  Qed.

  Theorem rpts_ref:
    (RPT0.rptM ⊕ SUCC.succM ⊕ PUT.putM)
      ⊑
      (RPT1.rptM "succ" (cfunU_int SUCC.succF)) ⊕ (RPT1.rptM "putOnce" (cfunU_int PUT.putOnceF)).
  Proof.
    pose proof rpts_ref_iprop. do 2 setoid_rewrite <- own_sep in H.
    eapply IPM.adequacy in H. rewrite oplus_assoc in H. eapply H.
  Qed.

End PROOF.

Section CCR.

  (* Definition α_conds (fn: string) (f: list val -> itree Es Z) : conds := *)
  Definition α (fn: string) (f: list val -> itree Es Z) : conds :=
    fun fn' => if (String.eqb fn fn') then
              mk_cond (fun args => exists (n: Z), args = ([Vint n])↑)
                      (fun args ret =>
                         exists (n r: Z), (args = ([Vint n])↑) /\ (ret = (Vint r)↑) /\
                                       (Ret ret ≈ (cfunU_int f) args))
            else ε.

  (* Definition α (fn: string) (f: list val -> itree Es Z) : conds_CM := *)
  (*   (α_conds fn f: conds_CM). *)

  (* Definition β_conds (fn: string) (f: list val -> itree Es Z) : conds := *)
  Definition β (fn: string) (f: list val -> itree Es Z) : conds :=
    fun fn' => if (String.eqb fn fn') then
              mk_cond (fun args =>
                         exists (fb: ((nat + string) * Z)%type) (n x: Z),
                           args = ([Vptr (fst fb) (snd fb); Vint n; Vint x])↑)
                      (fun args ret =>
                         exists (fb: ((nat + string) * Z)%type) (n x r: Z),
                           (args = ([Vptr (fst fb) (snd fb); Vint n; Vint x])↑) /\
                             (ret = (Vint r)↑) /\
                             (Ret ret ≈ (RPT1.fun_iter (cfunU_int f) (Z.to_nat n) (Ret (Vint x)↑))))
            else ε.

  (* Definition β (fn: string) (f: list val -> itree Es Z) : conds_CM := *)
  (*   β_conds fn f. *)

  (* TODO : notation *)

  (* Lemma rpt0_ccr_spec: *)
  (*   OwnM (RPT0.rptM) ⊢ *)
  (*        □ (∀ fn f, *)
  (*              (∀ c, (𝑤_{c} (𝑤_{α fn f} (OwnM (ONE.oneM fn f)))) *)
  (*                      ==∗ *)
  (*                      (𝑤_{((α fn f) ⊕ (β fn f)) ⊕ c} (OwnM (RPT1.rptM fn (cfunU_int f)))))). *)

  (*** TODO : help **)

  (* Let wrap := Wrap (W:=Hoare_WA). *)

  Notation "𝑊_{ a } b" := (Wrap (M:=(MRA_to_MRAS (@Mod_MRA Sk.gdefs))) a b) (at level 50).

  Lemma rpt0_ccr_spec:
    OwnM (RPT0.rptM) ⊢
         □ (∀ fn f,
               (∀ c, (𝑊_{c} (𝑊_{α fn f} (OwnM (ONE.oneM fn f))))
                       ==∗
                       (𝑊_{((α fn f) ⊕ (β fn f)) ⊕ c} (OwnM (RPT1.rptM fn (cfunU_int f)))))).
  Proof.
    iIntros "#RPT0". iModIntro. iIntros (fn f) "ONE".
    iPoseProof (own_sep with "[ONE RPT0]") as "OWN". iSplitL "RPT0". auto. iApply "ONE".
    iClear "RPT0".
    iStopProof. apply IPM.adequacy. apply one_rpt_ref.
  Qed.

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

End CCR.
