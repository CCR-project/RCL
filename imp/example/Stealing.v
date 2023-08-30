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

  (* If init is called more than two times, it is UB. *)
  Definition initF : list val -> itree Es val :=
    fun varg =>
      _ <- ((pargs [] varg)?);;
      v0 <- trigger PGet;;
      ` v1: (option val) <- (v0↓)?;;
      if (is_some v1)
      then triggerUB
      else _ <- trigger (PPut (Some (Vint 0%Z))↑);;
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
      ` v1: (option val) <- (v0↓)?;;
      ` _: val <- v1?;;
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
            (<<TGT: t = Any.pair (m↑) (Vnullptr↑)>>) /\
            (<<WFM: Mem.wf m>>)
      | S _ =>
          exists (v: val) (ms mt: Mem.t) (b: nat) (ofs: Z),
          (<<SRC: s = Any.pair (ms↑) ((Some v)↑)>>) /\
            (<<TGT: t = Any.pair (mt↑) ((Vptr (inl b) ofs)↑)>>) /\
            (<<VARNB: b < Mem.nb mt>>) /\
            (<<VART: Mem.cnts mt (inl b) ofs = Some v>>) /\
            (<<VARS: forall ofs0, Mem.cnts ms (inl b) ofs0 = None>>) /\
            (<<WFMS: Mem.wf ms>>) /\
            (<<WFMT: Mem.wf mt>>) /\
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

  Lemma mem_less_defined_free
        m0 m1
        (MLD: mem_less_defined m0 m1)
        b ofs m1'
        (FREE: Mem.free m1 b ofs = Some m1')
    :
    exists m0', Mem.free m0 b ofs = Some m0'.
  Proof. unfold Mem.free in *. des_ifs; eauto. apply MLD in Heq. clarify. Qed.

  Lemma mem_less_defined_load
        m0 m1
        (MLD: mem_less_defined m0 m1)
        b ofs v
        (LOAD: Mem.load m1 b ofs = Some v)
    :
    exists v', Mem.load m0 b ofs = Some v'.
  Proof.
    unfold Mem.load in *. destruct (Mem.cnts m0 b ofs) eqn:CASE; eauto.
    eapply MLD in CASE. clarify.
  Qed.

  Lemma mem_less_defined_store
        m0 m1
        (MLD: mem_less_defined m0 m1)
        b ofs v m1'
        (STORE: Mem.store m1 b ofs v = Some m1')
        v'
    :
    exists m0', Mem.store m0 b ofs v' = Some m0'.
  Proof. unfold Mem.store in *. des_ifs; eauto. apply MLD in Heq. clarify. Qed.

  Lemma mem_less_defined_vcmp
        m0 m1
        (MLD: mem_less_defined m0 m1)
        v0 v1 b
        (STORE: vcmp m1 v0 v1 = Some b)
    :
    vcmp m0 v0 v1 = Some b.
  Proof.
    unfold vcmp in *. des_ifs; eauto.
    - exfalso. simpl_bool. des; clarify.
      unfold Mem.valid_ptr, is_some in *. des_ifs. apply MLD in Heq2. clarify.
    - exfalso. simpl_bool. des; clarify.
      unfold Mem.valid_ptr, is_some in *. des_ifs. apply MLD in Heq2. clarify.
    - exfalso. simpl_bool. des; clarify.
      + clear Heq1. unfold Mem.valid_ptr, is_some in *. des_ifs. apply MLD in Heq1. clarify.
      + clear Heq0. unfold Mem.valid_ptr, is_some in *. des_ifs. apply MLD in Heq0. clarify.
  Qed.

  Lemma mem_wf_pad
        m
        (WF: Mem.wf m)
        sz m'
        (OP: Mem.mem_pad m sz = m')
    :
    Mem.wf m'.
  Proof.
    unfold Mem.wf, Mem.mem_pad in *. i. clarify. ss. apply WF; lia.
  Qed.

  Lemma mem_wf_alloc
        m
        (WF: Mem.wf m)
        sz b m'
        (OP: Mem.alloc m sz = (b, m'))
    :
    Mem.wf m'.
  Proof.
    unfold Mem.wf, Mem.alloc in *. i. clarify. ss. unfold update. des_ifs. lia.
    apply WF. lia.
  Qed.

  Lemma mem_wf_free
        m
        (WF: Mem.wf m)
        b ofs m'
        (OP: Mem.free m b ofs = Some m')
    :
    Mem.wf m'.
  Proof.
    unfold Mem.wf, Mem.free in *. i. des_ifs. ss. unfold update. des_ifs.
    - apply WF. auto.
    - apply WF. auto.
  Qed.

  Lemma mem_wf_store
        m
        (WF: Mem.wf m)
        b ofs v m'
        (OP: Mem.store m b ofs v = Some m')
    :
    Mem.wf m'.
  Proof.
    unfold Mem.wf, Mem.store in *. i. des_ifs. ss. des_ifs.
    - exfalso. simpl_bool. des. apply sumbool_to_bool_true in Heq0. clarify. eapply WF in LT.
      rewrite Heq in LT. clarify.
    - apply WF; auto.
  Qed.

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
            eapply mem_wf_alloc. eapply mem_wf_pad. eauto. eauto.
            unfold Mem.mem_pad, Mem.alloc. ss.
          }
          steps.
        }
        { des. hide_tgt. steps. subst hide_tgt. steps. rewrite _UNWRAPU0. steps.
          des_ifs.
          { steps. force_r. intros pad. force_l. exists (nbd + pad). steps.
            unfold lift_rel. exists (S w).
            replace (Mem.nb ms + (nbd + pad)) with (Mem.nb mt + pad). 2: lia.
            splits; auto.
            ss. exists v. do 2 eexists. exists b, ofs. splits. eauto. eauto. all: ss.
            - lia.
            - unfold update. des_ifs; try lia.
            - i. unfold update. des_ifs; try lia.
            - eapply mem_wf_alloc. eapply mem_wf_pad. eapply WFMS.
              instantiate (2:=(nbd + pad)). eauto.
              unfold Mem.mem_pad, Mem.alloc. ss. 
              replace (Mem.nb ms + (nbd + pad)) with (Mem.nb mt + pad). 2: lia. ss.
            - eapply mem_wf_alloc. eapply mem_wf_pad. eapply WFMT.
              instantiate (2:=(pad)). eauto.
              unfold Mem.mem_pad, Mem.alloc. ss. 
            - exists 0. lia.
            - ii. ss. unfold update in *. des_ifs. eapply MLD; eauto.
            - ii. ss. unfold update in *. des_ifs. eapply MCE; eauto.
          }
          steps.
        }
      - exists (focus_left (T:=Any.t) ∘ cfunU freeF). split. auto. ii. subst y.
        ginit.
        unfold_goal @freeF. unfold_goal @cfunU.
        destruct w; ss.
        { des. hide_tgt. steps. subst hide_tgt.
          steps. rewrite _UNWRAPU0.
          steps. rewrite _UNWRAPU1.
          steps. unfold lift_rel. exists 0. splits; auto. ss.
          eexists. splits; eauto.
          eapply mem_wf_free; eauto.
        }
        { des. hide_tgt. steps. subst hide_tgt. steps. rewrite _UNWRAPU0. steps.
          hexploit mem_less_defined_free; eauto. intros (mt' & FREETGT). rewrite FREETGT.
          steps. unfold lift_rel. exists (S w). splits; auto. ss.
          unfold Mem.free in FREETGT. des_ifs.
          unfold Mem.free in _UNWRAPU1. des_ifs.
          exists v. do 2 eexists. exists b, ofs. splits. 1,2: eauto. all: ss; eauto.
          - unfold update. des_ifs. rewrite VARS in Heq0. clarify.
          - i. unfold update. des_ifs.
          - eapply mem_wf_free. eapply WFMS. unfold Mem.free. rewrite Heq0. ss.
          - eapply mem_wf_free. eapply WFMT. unfold Mem.free. rewrite Heq. ss.
          - ii. ss. unfold update in *. des_ifs. all: apply MLD; auto.
          - ii. ss. unfold update in *. des_ifs. all: eapply MCE; eauto.
        }
      - exists (focus_left (T:=Any.t) ∘ cfunU loadF). split. auto. ii. subst y.
        ginit.
        unfold_goal @loadF. unfold_goal @cfunU.
        destruct w; ss.
        { des. hide_tgt. steps. subst hide_tgt.
          steps. rewrite _UNWRAPU0.
          steps. rewrite _UNWRAPU1.
          steps. unfold lift_rel. exists 0. splits; auto. ss.
          eexists. splits; eauto. 
        }
        { des. hide_tgt. steps. subst hide_tgt. steps. rewrite _UNWRAPU0. steps.
          hexploit mem_less_defined_load; eauto. intros (v' & LOADTGT). rewrite LOADTGT.
          steps. unfold lift_rel. exists (S w). splits; auto.
          { ss.
            unfold Mem.load in LOADTGT.
            unfold Mem.load in _UNWRAPU1.
            exists v. do 2 eexists. exists b, ofs. splits. 1,2: eauto. all: ss; eauto.
          }
          { symmetry. f_equal. eapply MCE; eauto. }
        }
      - exists (focus_left (T:=Any.t) ∘ cfunU storeF). split. right. auto. ii. subst y.
        ginit.
        unfold_goal @storeF. unfold_goal @cfunU.
        destruct w; ss.
        { des. hide_tgt. steps. subst hide_tgt.
          steps. rewrite _UNWRAPU0.
          steps. unfold lift_rel. exists 0. splits; auto. ss.
          eexists. splits; eauto. eapply mem_wf_store; eauto.
        }
        { des. hide_tgt. steps. subst hide_tgt. steps.
          hexploit mem_less_defined_store; eauto. intros (mt' & STORETGT). rewrite STORETGT.
          steps. unfold lift_rel. exists (S w). splits; auto. ss.
          unfold Mem.store in STORETGT. des_ifs.
          unfold Mem.store in _UNWRAPU0. des_ifs.
          exists v. do 2 eexists. exists b, ofs. splits. 1,2: eauto. all: ss; eauto.
          - des_ifs. exfalso. simpl_bool. des. apply sumbool_to_bool_true in Heq2, Heq3. clarify.
            rewrite VARS in Heq1. clarify.
          - i. des_ifs.
            exfalso. simpl_bool. des. apply sumbool_to_bool_true in Heq2, Heq3. clarify.
            rewrite VARS in Heq1; clarify.
          - eapply mem_wf_store. eapply WFMS. unfold Mem.store; rewrite Heq1. ss.
          - eapply mem_wf_store. eapply WFMT. unfold Mem.store; rewrite Heq. ss.
          - ii. ss. des_ifs. apply MLD; auto.
          - ii. ss. des_ifs. eapply MCE; eauto.
        }
      - exists (focus_left (T:=Any.t) ∘ cfunU cmpF). split. right. auto. ii. subst y.
        ginit.
        unfold_goal @cmpF. unfold_goal @cfunU.
        destruct w; ss.
        { des. hide_tgt. steps. subst hide_tgt.
          steps. rewrite _UNWRAPU0.
          steps. des_ifs; steps.
          - unfold lift_rel. exists 0. splits; auto. ss. eexists. splits; eauto.
          - unfold lift_rel. exists 0. splits; auto. ss. eexists. splits; eauto.
        }
        { des. hide_tgt. steps. subst hide_tgt. steps.
          hexploit mem_less_defined_vcmp; eauto. intros VCMPTGT. rewrite VCMPTGT.
          steps.
          assert (Q: forall rv, lift_rel var_sim_inv le (S w) eq (Any.pair (Any.upcast ms) (Any.upcast (Some v))) (Any.pair (Any.upcast mt) (Any.upcast (Vptr (inl b) ofs))) (Any.upcast (Vint rv)) (Any.upcast (Vint rv))).
          { i. unfold lift_rel. exists (S w). splits; auto. ss.
            exists v. do 2 eexists. exists b, ofs. splits. 1,2: eauto. all: ss; eauto.
          }
          des_ifs; steps.
        }

        (* VAR module *)
      - exists (focus_right (T:=Any.t) ∘ cfunU VAR0.initF). split. do 2 right. auto. ii. subst y.
        ginit.
        unfold_goal @VAR0.initF. unfold_goal @VAR1.initF. unfold_goal @cfunU.
        destruct w; ss.
        { des. steps.
          unfold ccallU. steps.
          instantiate (1:=focus_left (T:=Any.t) ∘ cfunU allocF). auto.
          unfold_goal @allocF. unfold_goal @cfunU. steps.
          instantiate (1:=focus_left (T:=Any.t) ∘ cfunU storeF). auto.
          unfold_goal @storeF. unfold_goal @cfunU. steps.
          unfold Mem.store. ss.
          replace 
            (update (Mem.cnts m) (inl (Mem.nb m + x0))
                    (fun ofs : Z => if (0 <=? ofs)%Z && (ofs <? 1)%Z then Some Vundef else None)
                    (inl (Mem.nb m + x0)) 0%Z)
            with
            (Some Vundef).
          2:{ unfold update. des_ifs. }
          set ({|
                  Mem.cnts :=
                  fun (_b : nat + string) (_ofs : Z) =>
                    if dec (inl (Mem.nb m + x0)) _b && dec 0%Z _ofs
                    then Some (Vint 0)
                    else
                      update (Mem.cnts m) (inl (Mem.nb m + x0))
                             (fun ofs : Z => if (0 <=? ofs)%Z && (ofs <? 1)%Z then Some Vundef else None) _b
                             _ofs;
                  Mem.nb := S (Mem.nb m + x0)
                |}) as mt'.
          steps. unfold lift_rel. exists 1. splits; auto. ss.
          exists (Vint 0). do 2 eexists. exists (Mem.nb m + x0), 0%Z. splits. 1,2: eauto. all: ss; auto.
          - simpl_bool. des_ifs. apply sumbool_to_bool_false in Heq0. ss.
          - i. eapply WFM. lia.
          - subst mt'. eapply mem_wf_store. eapply mem_wf_alloc. eapply mem_wf_pad.
            eapply WFM. instantiate (2:=x0). ss. instantiate (3:=1%Z). ss.
            instantiate (3:=inl (Mem.nb m + x0)). instantiate (2:=0%Z). instantiate (1:=Vint 0).
            unfold Mem.store. ss.
            replace (
    update (Mem.cnts m) (inl (Mem.nb m + x0))
      (fun ofs : Z => if (0 <=? ofs)%Z && (ofs <? 1)%Z then Some Vundef else None)
      (inl (Mem.nb m + x0)) 0%Z) with (Some Vundef).
            2:{ unfold update. des_ifs. }
            ss.
          - exists (S x0). lia.
          - ii. subst mt'. ss. des_ifs. unfold update in H. des_ifs. apply WFM. lia.
          - ii. subst mt'. ss. des_ifs.
            + simpl_bool. des. apply sumbool_to_bool_true in Heq0, Heq1. clarify.
              specialize (WFM (Mem.nb m + x0) 0%Z). rewrite WFM in H0 by lia; clarify.
            + unfold update in H. des_ifs.
              specialize (WFM (Mem.nb m + x0) ofs). rewrite WFM in H0 by lia; clarify.
        }
        { des. steps. }
      - exists (focus_right (T:=Any.t) ∘ cfunU VAR0.getF). split. do 3 right. auto. ii. subst y.
        ginit.
        unfold_goal @VAR0.getF. unfold_goal @VAR1.getF. unfold_goal @cfunU.
        destruct w; ss.
        { des. steps. }
        { des. steps.
          unfold ccallU. steps.
          instantiate (1:=focus_left (T:=Any.t) ∘ cfunU loadF). auto.
          unfold_goal @loadF. unfold_goal @cfunU. steps.
          unfold Mem.load. rewrite VART. steps.
          unfold lift_rel. exists (S w). splits; auto. ss.
          exists v. do 2 eexists. exists b, ofs. splits. 1,2: eauto. all: ss; eauto.
        }
      - exists (focus_right (T:=Any.t) ∘ cfunU VAR0.setF). split. do 4 right. auto. ii. subst y.
        ginit.
        unfold_goal @VAR0.setF. unfold_goal @VAR1.setF. unfold_goal @cfunU.
        destruct w; ss.
        { des. steps. }
        { des. steps.
          unfold ccallU. steps.
          instantiate (1:=focus_left (T:=Any.t) ∘ cfunU storeF). auto.
          unfold_goal @storeF. unfold_goal @cfunU. steps.
          unfold Mem.store. rewrite VART.
          set ({|
                  Mem.cnts :=
                  fun (_b : nat + string) (_ofs : Z) =>
                    if dec (inl b) _b && dec ofs _ofs then Some (Vint z) else Mem.cnts mt _b _ofs;
                  Mem.nb := Mem.nb mt
                |}) as mt'.
          steps. unfold lift_rel. exists (S w). splits; auto. ss.
          exists (Vint z). do 2 eexists. exists b, ofs. splits. 1,2: eauto. all: ss; eauto.
          - des_ifs. simpl_bool. des. 1,2: apply sumbool_to_bool_false in Heq; clarify.
          - subst mt'. eapply mem_wf_store. eapply WFMT. unfold Mem.store.
            rewrite VART. ss.
          - ii. ss. des_ifs. apply MLD; auto.
          - subst mt'. ii. ss. des_ifs.
            + simpl_bool. des. apply sumbool_to_bool_true in Heq. clarify.
              rewrite VARS in H0; clarify.
            + eapply MCE; eauto.
        }
    }
    { exists 0. ss. esplits; eauto. ss. }
  Qed.

  (* FIX: Qed takes too long *)

End PROOFSIM.
