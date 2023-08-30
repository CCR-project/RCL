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
Require Import Mem0.
Require Import HTactics.

Set Implicit Arguments.

Local Open Scope nat_scope.


Module VAR0.

  Definition initF : list val -> itree Es val :=
    fun varg =>
      _ <- ((pargs [] varg)?);;
      ` ptr: val <- ccallU "alloc" [Vint 1%Z];;
      ` _ : val <- ccallU "store" [ptr; (Vint 0%Z)];;
      _ <- trigger (PPut ptr↑);;
      Ret (Vint 0).

  Definition getF : list val -> itree Es val :=
    fun varg =>
      _ <- ((pargs [] varg)?);;
      ptr0 <- trigger (PGet);;
      ` ptr: val <- (ptr0↓)?;;
      ccallU "load" [ptr].

  Definition setF : list val -> itree Es val :=
    fun varg =>
      w <- ((pargs [Tint] varg)?);;
      ptr0 <- trigger (PGet);;
      ` ptr: val <- (ptr0↓)?;;
      ccallU "store" [ptr; (Vint w)].

  Definition varMS_ : ModSem._t :=
    {|
      ModSem.fnsems := [("init", cfunU initF); ("get", cfunU getF); ("set", cfunU setF)];
      ModSem.initial_st := Vnullptr↑;
    |}.

  Definition varMS : ModSem.t := Algebra.just varMS_.

End VAR0.

Module VAR1.

  Definition initF : list val -> itree Es val :=
    fun varg =>
      _ <- ((pargs [] varg)?);;
      _ <- trigger (PPut (Some (Vint 0%Z))↑);;
      Ret (Vint 0).

  Definition getF : list val -> itree Es val :=
    fun varg =>
      _ <- ((pargs [] varg)?);;
      v0 <- trigger (PGet);;
      ` v1: (option val) <- (v0↓)?;;
      ` v: val <- v1?;;
      Ret v.

  Definition setF : list val -> itree Es val :=
    fun varg =>
      w <- ((pargs [Tint] varg)?);;
      v0 <- trigger (PGet);;
      ` _: (option val) <- (v0↓)?;;
      _ <- trigger (PPut (Some (Vint w))↑);;
      Ret (Vint 0).

  Definition varMS_ : ModSem._t :=
    {|
      ModSem.fnsems := [("init", cfunU initF); ("get", cfunU getF); ("set", cfunU setF)];
      ModSem.initial_st := (@None val)↑;
    |}.

  Definition varMS : ModSem.t := Algebra.just varMS_.

End VAR1.

Section PROOFSIM.

  Import ModSemPair.

  Ltac ired_eq_l := (Red.prw IRed._red_gen 2 0).
  Ltac ired_eq_r := (Red.prw IRed._red_gen 1 0).

  Definition mem_less_defined (m0 m1: Mem.t) :=
    forall b ofs, (Mem.cnts m0 b ofs = None) -> (Mem.cnts m1 b ofs = None).

  Definition mem_cnt_eq (m0 m1: Mem.t) :=
    forall b ofs v1 v2,
      (Mem.cnts m0 b ofs = Some v1) -> (Mem.cnts m1 b ofs = Some v2) -> v1 = v2.

  Definition var_sim_inv : nat -> (Any.t * Any.t) -> Prop :=
    fun n '(s, t) =>
      match n with
      | O =>
          exists (m: Mem.t),
          (<<SRC: s = Any.pair (m↑) ((@None val)↑)>>) /\
            (<<TGT: t = Any.pair (m↑) (Vnullptr↑)>>)
            (* (<<WFM: Mem.wf m>>) *)
      | S _ =>
          exists (v: val) (ms mt: Mem.t) (b: nat) (ofs: Z),
          (<<SRC: s = Any.pair (ms↑) ((Some v)↑)>>) /\
            (<<TGT: t = Any.pair (mt↑) ((Vptr (inl b) ofs)↑)>>) /\
            (<<VARNB: b < Mem.nb mt>>) /\
            (<<VART: Mem.load mt (inl b) ofs = Some v>>) /\
            (<<VARS: forall ofs0, Mem.cnts ms (inl b) ofs0 = None>>) /\
            (* (<<WFMS: Mem.wf ms>>) /\ *)
            (* (<<WFMT: Mem.wf mt>>) /\ *)
            (<<NBLK: exists nbd, (Mem.nb mt) = (Mem.nb ms) + nbd>>) /\
            (<<MLD: mem_less_defined mt ms>>) /\
            (<<MCE: mem_cnt_eq mt ms>>)
      end.

  Ltac unfold_goal H :=
    match goal with
    | [|- gpaco8 (_sim_itree ?_temp1 _ _) (cpn8 (_sim_itree ?_temp2 _ _)) _ _ _ _ _ _ _ _ _ _] =>
        let tvar1 := fresh "temp1" in
        let tvar2 := fresh "temp2" in
        remember _temp1 as tvar1; remember _temp2 as tvar2; unfold H; subst tvar1 tvar2
    end.

  Ltac hide_src :=
    match goal with
    | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, _)) ] =>
        let hsrc := fresh "hide_src" in set i_src as hsrc at 1
    end.

  Ltac hide_tgt :=
    match goal with
    | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, ?i_tgt)) ] =>
        let htgt := fresh "hide_tgt" in set i_tgt as htgt at 2
    end.

  Lemma var_sim:
    ModSemPair.sim ((MemSem Sk.unit) ⊕ VAR1.varMS) ((MemSem Sk.unit) ⊕ VAR0.varMS).
  Proof.
    Local Opaque String.eqb.
    ss. eapply (@mk _ _ _ var_sim_inv _ Nat.le_preorder).
    { i. ss. des; clarify.
      - exists (focus_left (T:=Any.t) ∘ cfunU allocF). split. auto. ii. subst y.
        ginit.
        unfold_goal @allocF. unfold_goal @cfunU.
        destruct w; ss.
        { des. hide_tgt. steps. subst hide_tgt. steps.
          rewrite _UNWRAPU0. steps. des_ifs.
          { hide_tgt. steps. subst hide_tgt. steps. hide_src. force_r. intros pad.
            steps. subst hide_src. force_l. exists pad. steps.
            unfold lift_rel. exists 0. splits; auto. ss. esplits; eauto.
          }
          steps.
        }
        des. hide_tgt. steps. subst hide_tgt. steps. rewrite _UNWRAPU0. steps.
        des_ifs.
        { steps. force_r. intros pad. force_l. exists (nbd + pad). steps.
          unfold lift_rel. exists (S w).
          replace (Mem.nb ms + (nbd + pad)) with (Mem.nb mt + pad). 2: lia.
          splits; auto.
          - ss. exists v. do 2 eexists. exists b, ofs. splits. eauto. eauto. all: ss.
            + lia.
            + unfold update. des_ifs; try lia.
            + i. unfold update. des_ifs; try lia.
            + exists 0. lia.
            + ii. ss. unfold update in *. des_ifs. eapply MLD; eauto.
            + ii. ss. unfold update in *. des_ifs. eapply MCE; eauto.
        }
        steps.
      - exists (focus_left (T:=Any.t) ∘ cfunU freeF). split. auto. ii. subst y.
        ginit.
        unfold_goal @freeF. unfold_goal @cfunU.
        destruct w; ss.
        { des. hide_tgt. steps.
          (* match goal with *)
          (* | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, unleftU ?ox >>= _) (_, _)) ] => *)
          (*     let tvar := fresh "tmp" in *)
          (*     let thyp := fresh "TMP" in *)
          (*     remember (unleftU ox) as tvar eqn:thyp; unfold unleftU in thyp; subst tvar; *)
          (*     let name := fresh "_UNLEFTU" in *)
          (*     destruct (ox) eqn:name; [|unfold triggerUB; ired_both; _force_l; ss; fail] *)
          (* end. *)
          (* TODO *)

          unfold unleftU. steps.
          rewrite _UNWRAPU0. steps. des_ifs.
          { hide_tgt. steps. subst hide_tgt. steps. hide_src. force_r. intros pad.
            steps. subst hide_src. force_l. exists pad. steps.
            unfold lift_rel. exists 0. splits; auto. ss. esplits; eauto.
          }
          steps.
        }
        des. hide_tgt. steps. subst hide_tgt. steps. rewrite _UNWRAPU0. steps.
        des_ifs.
        { steps. force_r. intros pad. force_l. exists (nbd + pad). steps.
          unfold lift_rel. exists (S w).
          replace (Mem.nb ms + (nbd + pad)) with (Mem.nb mt + pad). 2: lia.
          splits; auto.
          - ss. exists v. do 2 eexists. exists b, ofs. splits. eauto. eauto. all: ss.
            + lia.
            + unfold update. des_ifs; try lia.
            + i. unfold update. des_ifs; try lia.
            + exists 0. lia.
            + ii. ss. unfold update in *. des_ifs. eapply MLD; eauto.
            + ii. ss. unfold update in *. des_ifs. eapply MCE; eauto.
        }
        steps.
      -
        
              

          (* TODO *)

        
        
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

End PROOFSIM.
