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

End SUCC.

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

  Fixpoint fun_iter (f: Any.t -> itree Es Any.t) (n: nat) (x: itree Es Any.t): itree Es Any.t :=
    match n with
    | O => x
    | S n' => fun_iter f n' (x >>= f)
    end.

  Definition rptF (fn: string) (f: Any.t -> itree Es Any.t) : list val -> itree Es val :=
    fun varg =>
      '(fb, (n, x)) <- (pargs [Tptr; Tint; Tint] varg)?;;
      fn0 <- ((unname (Vptr (fst fb) (snd fb)))?);;
      if (String.eqb fn fn0)
      then
        assume(intrange_64 n);;;
        vret <- (fun_iter f (Z.to_nat n) (Ret (Vint x)↑));;
        ` vret0: val <- unwrapU vret↓;; Ret vret0
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

Section PROOF.

  Import Red IRed.
  Import SimDTree.
  Import ModSemPair.
  (* Import TAC. *)

  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Lemma succ_rpt_sim:
    ModSemPair.sim (RPT1.rptMS "succ" (cfunU SUCC.succF)) (RPT0.rptMS ⊕ SUCC.succMS).
  Proof.
    ss. eapply mk. eapply Nat.le_preorder. instantiate (1:= fun _ _ => True).
    { i. ss. des; clarify. exists (cfunU RPT0.rptF). split.
      { left. f_equal. unfold RPT0.rptF, cfunU. extensionalities x.
        admit "".
      }
      unfold RPT1.rptF. unfold RPT0.rptF at 2. unfold cfunU at 3. unfold cfunU at 4.
      unfold sim_fsem. ii. subst y.
      ginit. 


End PROOF.
