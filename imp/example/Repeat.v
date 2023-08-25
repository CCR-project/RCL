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

End RPT1.



Section PROOFSIM.

  Import ModSemPair.

  Ltac ired_eq_l := (Red.prw IRed._red_gen 2 0).
  Ltac ired_eq_r := (Red.prw IRed._red_gen 1 0).

  Lemma Z_to_nat_le_zero z: 0 = Z.to_nat z -> (z <= 0)%Z.
  Proof. intros. unfold Z.to_nat in H. des_ifs. pose proof (Pos2Nat.is_pos p). lia. Qed.

  Lemma Z_to_nat_ge_one z: forall n, S n = Z.to_nat z -> (z >= 1)%Z.
  Proof. intros. unfold Z.to_nat in H. des_ifs. lia. Qed.

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
      destruct (eqb_spec "succ" s).
      2:{ steps. }
      clarify.
      steps. force_r. eexists; auto.
      steps. rename z0 into v.
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
        { clear - _ASSUME ZRANGE. unfold_intrange_64.
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
          auto. f_equal. ired_eq_l. auto.
        }
        { steps. irw in IHn.
          guclo guttC_spec. econs. eapply IHn.
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
      destruct (eqb_spec "putOnce" s).
      2:{ steps. }
      clarify.
      steps. force_r. eexists; auto.
      steps. rename z0 into v.
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
        { clear - _ASSUME ZRANGE. unfold_intrange_64.
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
          auto. f_equal. ired_eq_l. auto.
        }
        { steps. irw in IHn.
          guclo guttC_spec. econs. eapply IHn.
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

End PROOFSIM.
