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

Require Import IPM IPMAux Hoare.


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


Definition cast_val (body: Z -> itree Es Z): list val -> itree Es val :=
  fun varg =>
    z <- ((pargs [Tint] varg)?);;
    vret <- body z;; Ret (Vint vret).

Definition cfunU_int (body: Z -> itree Es Z): Any.t -> itree Es Any.t :=
  cfunU (cast_val body).

Module ONE.

  Definition oneMS_ (fn: string) (f: Z -> itree Es Z): ModSem._t :=
    {|
      ModSem.fnsems := [(fn, cfunU_int f)];
      ModSem.initial_st := tt↑;
    |}.

  Definition oneMS (fn: string) (f: Z -> itree Es Z): ModSem.t :=
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

Notation fzz := (Z -> Z).
Definition SEs := (pE +' eventE).

Section EMBED.

  Definition embed (se: Z -> itree SEs Z) (cp: fzz): Z -> itree Es Z :=
    fun z =>
      _ <- (resum_itr (se z));;
      Ret (cp z).

End EMBED.

Module SUCC.

  Definition succF : Z -> itree Es Z := embed (fun z => Ret z) (fun z => (z + 1)%Z).

  Definition succM : Mod.t := ONE.oneM "succ" succF.

End SUCC.

Module PUT.

  Definition putOnceF : Z -> itree Es Z :=
    embed (fun z => _ <- trigger (Syscall "print" ((Vint z)↑) top1);; Ret 0%Z) (fun z => z).

  Definition putM : Mod.t := ONE.oneM "putOnce" putOnceF.

End PUT.


Section PROOFSIM.

  Import ModSemPair.

  Lemma Z_to_nat_le_zero z: 0 = Z.to_nat z -> (z <= 0)%Z.
  Proof. intros. unfold Z.to_nat in H. des_ifs. pose proof (Pos2Nat.is_pos p). lia. Qed.

  Lemma Z_to_nat_ge_one z: forall n, S n = Z.to_nat z -> (z >= 1)%Z.
  Proof. intros. unfold Z.to_nat in H. des_ifs. lia. Qed.

  Lemma one_rpt_sim
        (fn': string) (f': Z -> itree Es Z)
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



Notation "𝑊_{ a } b" := (Wrap (M:=(MRA_to_MRAS (@Mod_MRA Sk.gdefs))) a b) (at level 50).
Notation "𝑀_{ a } b" := (Wrap2 (M:=(MRA_to_MRAS (@Mod_MRA Sk.gdefs))) a b) (at level 50).

Section AUX.

  (* FIXME : fix wrap-ired interaction and move *)
  Import IRed.
  Global Program Instance wrap_rdb: red_database (mk_box (@wrap_itree)) :=
    mk_rdb
      0
      (mk_box wrap_bind)
      (mk_box wrap_tau)
      (mk_box wrap_ret)
      (mk_box wrap_pE)
      (mk_box wrap_pE)
      (mk_box wrap_callE)
      (mk_box wrap_eventE)
      (mk_box wrap_triggerUB)
      (mk_box wrap_triggerNB)
      (mk_box wrap_unwrapU)
      (mk_box wrap_unwrapN)
      (mk_box wrap_unleftU)
      (mk_box wrap_unleftN)
      (mk_box wrap_unrightU)
      (mk_box wrap_unrightN)
      (mk_box wrap_assume)
      (mk_box wrap_guarantee)
      (mk_box wrap_ext)
  .

End AUX.

Section EMBEDAUX.

  Fixpoint fzz_fun_iter (f: fzz) (n: nat) (x: Z) :=
    match n with
    | O => x
    | S n' => fzz_fun_iter f n' (f x)
    end.

  Lemma fzz_fun_iter_red f n x: fzz_fun_iter f (S n) x = fzz_fun_iter f n (f x).
  Proof. ss. Qed.


  Lemma red_embed se cp v:
    (cfunU (cast_val (embed se cp)) (Any.upcast [Vint v])) =
      ((cfunU (cast_val (fun z => resum_itr (se z))) (Any.upcast [Vint v]));;; Ret (Vint (cp v))↑).
  Proof.
    unfold cfunU, cast_val, embed. rewrite Any.upcast_downcast. grind.
  Qed.

  Import Red IRed.

  Ltac my_red_both := try (prw _red_gen 2 0); try (prw _red_gen 1 0).
  Ltac wrb := repeat (unfold wrap; my_red_both).

  Lemma wrap_itree_se:
    ∀ (cs : conds) [T : Type] (e : SEs T),
      wrap_itree cs (trigger e) = ` r : T <- trigger e;; (tau;; Ret r).
  Proof.
    i. destruct e.
    - match goal with | [ |- ?a = _] => replace a with (𝑤_{cs} trigger p) end.
      2:{ grind. }
      rewrite wrap_pE. grind.
    - match goal with | [ |- ?a = _] => replace a with (𝑤_{cs} trigger e) end.
      2:{ grind. }
      rewrite wrap_eventE. grind.
  Qed.

  Lemma wrap_itree_tau: ∀ (cs : conds) [A : Type] (itr : itree Es A), wrap_itree cs (tau;; itr) = (tau;; 𝑤_{ cs} itr).
    Proof. ii. rewrite <- wrap_tau. grind. Qed.

  Lemma wrap_itree_se_euttge
        T (se: itree SEs T) (c: conds)
    :
    wrap_itree c (resum_itr se) ≳ resum_itr se.
  Proof.
    revert_until T.
    ginit. gcofix CIH. i. ides se.
    - gstep. wrb. refl.
    - wrb. gstep. econs. gbase. auto.
    - rewrite <- bind_trigger. resub. wrb. rewrite wrap_itree_se. wrb. rewrite ! bind_trigger.
      gstep. econs. i. ss. wrb. gstep. eapply EqTauL. ss. grind. rewrite wrap_itree_tau.
      grind. eapply EqTau. wrb. gbase. auto.
  Qed.

  Lemma wrap_itree_focus_right_euttge
        X (e: SEs X) (c: conds)
    :
    wrap_itree c (focus_right (trigger e)) ≳ focus_right (trigger e).
  Proof.
    ginit. destruct e.
    - grind. resub. wrb. destruct p; grind; wrb.
      + rewrite ! bind_trigger. gstep. econs. i; ss. grind.
        repeat (gstep; econs; grind). unfold unwrapU. des_ifs.
        * grind.
          unfold wrap_itree. grind. rewrite unfold_interp. grind. econs. i; ss. grind.
          repeat (gstep; econs; grind). refl.
        * grind.
          unfold wrap_itree. grind. rewrite unfold_interp. grind. econs. i; ss.
      + rewrite ! bind_trigger. gstep. econs. i; ss. grind.
        repeat (gstep; econs; grind). unfold unwrapU. des_ifs.
        * grind.
          unfold wrap_itree. grind. refl.
        * grind.
          unfold wrap_itree. grind. rewrite unfold_interp. grind. econs. i; ss.
    - grind. resub. wrb. rewrite ! bind_trigger. gstep. econs. i; ss. grind.
      gstep; econs; wrb. gstep; econs; wrb. ss. 
      unfold wrap_itree. grind. refl.
  Qed.

  Lemma wrap_itree_focus_right_se_euttge
        T (se: itree SEs T) (c: conds)
    :
    wrap_itree c (focus_right (resum_itr se)) ≳ focus_right (resum_itr se).
  Proof.
    revert_until T.
    ginit. gcofix CIH. i. ides se.
    - gstep. wrb. refl.
    - wrb. gstep. econs. gbase. auto.
    - rewrite <- bind_trigger. resub. wrb.
      guclo eqit_clo_bind. econs.
      { eapply wrap_itree_focus_right_euttge. }
      i; clarify. wrb. gstep. econs. wrb. gbase. auto.
  Qed.

End EMBEDAUX.

Opaque fzz_fun_iter.


Section CCR.

  (* Definition α (fn: string) (f: list val -> itree Es Z) : conds := *)
  (*   fun fn' => if (String.eqb fn fn') then *)
  (*             mk_cond (fun args => exists (n: Z), args = ([Vint n])↑) *)
  (*                     (fun args ret => *)
  (*                        exists (n r: Z), (args = ([Vint n])↑) /\ (ret = (Vint r)↑) /\ *)
  (*                                      (Ret ret ≈ (cfunU_int f) args)) *)
  (*           else ε. *)

  Definition β (fn: string) (cp: fzz) : conds :=
    fun fn' => if (String.eqb fn fn') then
              mk_cond (fun args =>
                         exists (fb: ((nat + string) * Z)%type) (n x: Z),
                           (args = ([Vptr (fst fb) (snd fb); Vint n; Vint x])↑) /\
                             (fst fb = inr fn))
                      (fun args ret =>
                         exists (fb: ((nat + string) * Z)%type) (n x r: Z),
                           (args = ([Vptr (fst fb) (snd fb); Vint n; Vint x])↑) /\
                             (ret = (Vint r)↑) /\
                             (r = fzz_fun_iter cp (Z.to_nat n) x))
            else ε.

  (* FIXME *)
  Ltac wrap_steps := unfold_goal @wrap; steps.
  Ltac wraps := repeat (try wrap_steps).

  Lemma one_rpt_ccr_sim
        (fn: string) (se: Z -> itree SEs Z) (cp: fzz) (c: conds)
    :
    ModSemPair.sim (𝑤_{ (β fn cp) ⊕ c} RPT1.rptMS fn (cfunU_int (embed se cp)))
                   (𝑤_{ c} (RPT0.rptMS ⊕ ONE.oneMS fn (embed se cp))).
  Proof.
    Local Opaque String.eqb. Import ModSemPair.
    ss. eapply mk. eapply (@top2_PreOrder unit). instantiate (1:= (fun _ '(src, tgt) => exists tgt_l, tgt = Any.pair tgt_l src)).
    { i. ss. des; clarify.
      inv FINDS.
      exists (snd (𝑤_{ c} ("rpt", focus_left (T:=Any.t) <*> cfunU RPT0.rptF))). split.
      { left. ss. }
      ii. subst y. ginit.
      unfold_goal @wrap. ss. unfold_goal @wrap. steps.
      des. steps. force_r. clarify. wraps.
      unfold_goal RPT1.rptF. unfold_goal RPT0.rptF. unfold_goal @cfunU.
      unfold_goal @cfunU_int.
      wraps.

      destruct p0. unfold unptr, unint, unr in *. des_ifs_safe. ss; clarify.
      clear e0.
      destruct (String.eqb_spec fn s).
      2:{ steps. }
      clarify. wraps.
      rename z0 into v. remember (Z.to_nat z) as n. clear _ASSUME1.

      match goal with
      | [ |- gpaco8 _ _ _ _ _ _ _ _ _ _ _ (_, ?t1)] =>
          replace t1 with
          (` x2 : Any.t <-
                    (` x0 : val <- wrap_itree c (focus_left
                                                  (if Z_lt_le_dec z 1
                                                   then Ret (Vint v)
                                                   else
                                                     ` fn : string <- Ret s;;
                                                            ` v0 : val <- ccallU fn [Vint v];; ccallU "rpt" [Vptr (inr s) 0; Vint (z - 1); v0]));;
                            ` x1 : Any.t <- wrap_itree c (focus_left (Ret (Any.upcast x0)));; Ret x1);;
                  (guarantee (postcond (c "rpt") x x2);;; Ret x2))
      end.
      2:{ grind. }

      match goal with
      | [ |- gpaco8 _ _ _ _ _ _ _ _ _ _ (_, ?t1) _] =>
          replace t1 with
          (` x2 : Any.t <- (` r : Any.t <-
                                   wrap_itree (β s cp ⊕ c)
                                              (RPT1.fun_iter (cfunU (cast_val (embed se cp))) n
                                                             (Ret (Any.upcast (Vint v))));;
                                 ` x0 : val <-
                                          wrap_itree (β s cp ⊕ c) (` vret0 : val <- unwrapU (Any.downcast r);; Ret vret0);;
                                        ` x1 : Any.t <- wrap_itree (β s cp ⊕ c) (Ret (Any.upcast x0));; Ret x1);;
                  (guarantee (postcond (β s cp "rpt") x x2 ∧ postcond (c "rpt") x x2);;; Ret x2))
      end.
      2:{ grind. }

      guclo lbindC_spec. econs.
      { instantiate
          (2:= (fun src tgt r_s r_t =>
                  (exists tgt_l, tgt = Any.pair tgt_l src) /\
                    (r_s = r_t) /\ (exists (v: val), r_t = v↑) /\
                    (postcond (β s cp "rpt") x r_s))).

        revert x z v _UNWRAPU _ASSUME _ASSUME0 _ASSUME2 Heqn mrs_src tgt_l.
        induction n; intros.
        { hexploit Z_to_nat_le_zero; eauto. intros. des_ifs.
          2:{ lia. }
          ss. wraps.
          splits; eauto. unfold β. des_ifs. ss.
          apply Any.downcast_upcast in _UNWRAPU. des. clarify.
          exists (inr s, 0%Z). esplits; eauto. rewrite <- Heqn. ss.
        }
        { hexploit Z_to_nat_ge_one; eauto. intros ZRANGE. des_ifs. clear l.
          ss. unfold ccallU. wraps.
          { right; left. ss. }
          ss. force_r. clarify. wraps.
          unfold_goal @cfunU_int.
          rewrite (red_embed se cp v). wraps.
          guclo lbindC_spec. econs.
          { unfold_goal @cfunU. unfold_goal @cast_val. wraps.
            guclo lbindC_spec. econs.
            { guclo guttC_spec. econs.
              2: eapply wrap_itree_se_euttge. 2: eapply wrap_itree_focus_right_se_euttge.
              guclo lflagC_spec. econs.
              gfinal. right.
              eapply sim_itree_fsubset.
              2:{ eapply sim_itree_tgtr. eapply self_sim_itree.
                  ss. ii. split; ii.
                  - des. clarify. eauto.
                  - des. esplits; eauto.
              }
              ss. all: auto.
            }
            i. wraps.
            instantiate (1:= fun ss st rs rt => (exists st2, st = Any.pair st2 ss) /\ (rs = rt)).
            rr in SIM. des. subst. esplits; auto.
          }
          i. wraps.
          force_r. clarify.
          wraps.
          { left. ss. }
          unfold_goal @cfunU. unfold_goal RPT0.rptF. wraps.
          force_r.
          { clarify. }
          wraps.
          force_r.
          { exfalso. apply _ASSUME5. clear - _ASSUME2 ZRANGE. unfold_intrange_64.
            des_ifs. apply sumbool_to_bool_true in _ASSUME2, H.
            apply andb_true_intro. split; apply sumbool_to_bool_is_true; lia.
          }
          wraps.
          simpl in SIM. des. subst.
          specialize (IHn ([Vptr (inr s) 0; Vint (z - 1); Vint (cp v)]↑) (z - 1)%Z (cp v)).
          exploit IHn; auto.
          { lia. }
          clear IHn; intros IHn. des_ifs.
          { wraps. force_r.
            { apply _ASSUME6 in _GUARANTEE2. inv _GUARANTEE2. }
            wraps. guclo guttC_spec. econs.
            { match goal with
              | [IHn: gpaco8 _ _ _ _ _ _ ?RR0 _ _ _ _ _ |-
                   gpaco8 _ _ _ _ _ _ ?RR1 _ _ _ _ _] =>
                  replace RR1 with RR0
              end.
              { guclo lflagC_spec. econs. eapply IHn. all: auto. }
              { clear IHn. apply Any.downcast_upcast in _UNWRAPU. des.
                extensionalities. apply Axioms.prop_ext. split; ii.
                - des. subst. esplits; eauto. clear - H6 Heqn. unfold β in *. des_ifs; ss.
                  des. clarify. exists fb. exists z, v. destruct fb. ss.
                  apply Any.upcast_inj in H6. des; clarify. apply JMeq_eq in EQ0. clarify.
                  esplits; eauto. rewrite Z2Nat.inj_sub. 2: lia. rewrite <- Heqn. ss.
                  rewrite Nat.sub_0_r. ss.
                - des. subst. esplits; eauto. clear - H6 Heqn. unfold β in *. des_ifs; ss.
                  des. clarify. exists fb. exists (z - 1)%Z, (cp v). destruct fb. ss.
                  apply Any.upcast_inj in H6. des; clarify. apply JMeq_eq in EQ0. clarify.
                  esplits; eauto. rewrite Z2Nat.inj_sub. 2: lia. rewrite <- Heqn. ss.
                  rewrite Nat.sub_0_r. ss.
              }
            }

            - unfold cfunU. refl.
            - ired_eq_r. unfold wrap. ired_eq_r. unfold wrap. ired_eq_r. refl.
          }
          { wraps.
            match goal with
            | [ |- gpaco8 _ _ _ _ _ _ _ _ _ _ (_, ?t1) _] =>
                rewrite (bind_ret_r_rev t1)
            end.

            match goal with
            | [ |- gpaco8 _ _ _ _ _ _ _ _ _ _ _ (_, ?t1)] =>
                replace t1 with
    (` x1 : Any.t <- (` r : val <- wrap_itree c (focus_left (ccallU s [Vint (cp v)]));;
    ` x0 : val <-
    wrap_itree c (focus_left (ccallU "rpt" [Vptr (inr s) 0; Vint (z - 1 - 1); r]));;
           ` x1 : Any.t <- wrap_itree c (focus_left (Ret (Any.upcast x0)));; Ret x1);;
    ` x2 : Any.t <-
    (guarantee (postcond (c "rpt") (Any.upcast [Vptr (inr s) 0; Vint (z - 1); Vint (cp v)]) x1);;;
     Ret x1);;
    ` x3 : Any.t <-
    (assume (postcond (c "rpt") (Any.upcast [Vptr (inr s) 0; Vint (z - 1); Vint (cp v)]) x2);;;
     Ret x2);;
    ` x4 : Any.t <- (tau;; Ret x3);;
    ` x5 : Any.t <- wrap_itree c (tau;; Ret x4);;
    ` x6 : val <-
    wrap_itree c (focus_left (` vret : val <- unwrapU (Any.downcast x5);; Ret vret));;
    ` x7 : Any.t <- wrap_itree c (focus_left (Ret (Any.upcast x6)));; Ret x7)
            end.
            2:{ grind. }

            guclo lbindC_spec. econs.
            { instantiate
                (2:= (fun src tgt r_s r_t =>
                        (exists tgt_l, tgt = Any.pair tgt_l src) /\
                          (r_s = r_t) /\ (exists (v: val), r_t = v↑) /\
                          (postcond (β s cp "rpt") x r_s))).

              guclo guttC_spec. econs.
              { match goal with
                | [IHn: gpaco8 _ _ _ _ _ _ ?RR0 _ _ _ _ _ |-
                     gpaco8 _ _ _ _ _ _ ?RR1 _ _ _ _ _] =>
                    replace RR1 with RR0
                end.
                { guclo lflagC_spec. econs. eapply IHn. all: auto. }
                { clear IHn. apply Any.downcast_upcast in _UNWRAPU. des.
                  extensionalities. apply Axioms.prop_ext. split; ii.
                  - des. subst. esplits; eauto. clear - H6 Heqn. unfold β in *. des_ifs; ss.
                    des. clarify. exists fb. exists z, v. destruct fb. ss.
                    apply Any.upcast_inj in H6. des; clarify. apply JMeq_eq in EQ0. clarify.
                    esplits; eauto. rewrite Z2Nat.inj_sub. 2: lia. rewrite <- Heqn. ss.
                    rewrite Nat.sub_0_r. ss.
                  - des. subst. esplits; eauto. clear - H6 Heqn. unfold β in *. des_ifs; ss.
                    des. clarify. exists fb. exists (z - 1)%Z, (cp v). destruct fb. ss.
                    apply Any.upcast_inj in H6. des; clarify. apply JMeq_eq in EQ0. clarify.
                    esplits; eauto. rewrite Z2Nat.inj_sub. 2: lia. rewrite <- Heqn. ss.
                    rewrite Nat.sub_0_r. ss.
                }
              }

              - unfold cfunU. refl.
              - ired_eq_r. repeat (unfold wrap; try ired_eq_r). refl.
            }
            { clear IHn. ss. i; des. subst. wraps. force_r.
              exfalso. clear - _GUARANTEE2 _ASSUME6. clarify.
              wraps. esplits; eauto.
            }
          }
        }
      }
      { ss; ii. des; clarify. wraps. force_l.
        { exfalso. apply _GUARANTEE0. splits; auto. }
        wraps. exists tt. splits; eauto.
      }
    }
    { ss. exists tt. eauto. }
    Unshelve. all: auto. apply Any.upcast_downcast.
    { clear - _UNWRAPU _ASSUME Heqn. unfold β in *. des_ifs; ss.
      des. exists fb. destruct fb; ss; clarify. rewrite Any.upcast_downcast in _UNWRAPU.
      clarify. esplits; eauto.
    }
  Qed.

  Theorem one_rpt_ccr_ref fn se cp (c: conds_CM):
    𝑤_{ c} (RPT0.rptM ⊕ ONE.oneM fn (embed se cp)) ⊑
      𝑤_{ β fn cp ⊕ c} RPT1.rptM fn (cfunU_int (embed se cp)).
  Proof.
    eapply LSimMod. ss. ss. i. eapply ModSemPair.adequacy. apply one_rpt_ccr_sim.
  Qed.

  Lemma rpt0_ccr_spec:
    OwnM (RPT0.rptM) ⊢
         □ (∀ fn se cp,
               (∀ c, 𝑀_{c} (
                         (𝑊_{c} (OwnM (ONE.oneM fn (embed se cp))))
                           ==∗
                           (𝑊_{(β fn cp) ⊕ c} (OwnM (RPT1.rptM fn (cfunU_int (embed se cp)))))))).
  Proof.
    iIntros "#RPT0". iModIntro. iIntros (fn se cp c) "".
    iApply wrap2_adj1. 2: iApply "RPT0". iIntros "RPT0 ONE".
    iPoseProof (wrap_own with "RPT0") as "RPT0".
    iPoseProof (wrap_own with "ONE") as "ONE".
    iCombine "RPT0 ONE" as "TGT". rewrite WA.morph_oplus.
    iApply wrap_own.
    iStopProof. apply IPM.adequacy.
    apply one_rpt_ccr_ref.
  Qed.

End CCR.
