Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import ModSem.
Require Import Behavior.
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
Require Import Any.

Set Implicit Arguments.

Local Open Scope nat_scope.






Section SIM.
  Let st_local: Type := (Any.t).

  Variable world: Type.

  Let W: Type := (Any.t) * (Any.t).
  Variable wf: world -> W -> Prop.
  Variable le: relation world.


  Inductive _sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | sim_itree_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          sim_itree _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                 (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                 (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itree_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_choose_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: exists (x: X), _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itree_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itree_pput_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      st_src1
      (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itree_pget_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
                 (st_tgt0, i_tgt)


  | sim_itree_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itree_take_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: exists (x: X), _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Take X) >>= k_tgt)

  | sim_itree_pput_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      st_tgt1
      (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | sim_itree_pget_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
    :
      _sim_itree sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PGet) >>= k_tgt)

  | sim_itree_progress
      i_src0 i_tgt0 w0 st_src0 st_tgt0 i_src i_tgt
      (SIM: sim_itree _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
      (SRC: i_src0 = true)
      (TGT: i_tgt0 = true)
    :
      _sim_itree sim_itree RR true true w0 (st_src0, i_src) (st_tgt0, i_tgt)
  .

  Definition lift_rel {R_src R_tgt} (w0: world) (RR: R_src -> R_tgt -> Prop)
             (st_src st_tgt: st_local) (ret_src ret_tgt : Any.t) :=
    exists w1 : world,
      (<<WLE: le w0 w1 >> /\ <<WF: wf w1 (st_src, st_tgt) >> /\ <<RET: ret_src = ret_tgt >>).

  Lemma _sim_itree_ind2 (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        (P: bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        (RET: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            v_src v_tgt
            (RET: RR st_src0 st_tgt0 v_src v_tgt),
            P i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt)))
        (CALL: forall
            i_src0 i_tgt0 w w0 st_src0 st_tgt0
            fn varg k_src k_tgt
            (WF: wf w0 (st_src0, st_tgt0))
            (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
                sim_itree _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret)),
            P i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
              (st_tgt0, trigger (Call fn varg) >>= k_tgt))
        (SYSCALL: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            fn varg rvs k_src k_tgt
            (K: forall vret,
                sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
              (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt))
        (TAUSRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt))
        (CHOOSESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: exists (x: X), <<SIM: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
              (st_tgt0, i_tgt))
        (TAKESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: forall (x: X), <<SIM: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
              (st_tgt0, i_tgt))
        (PPUTSRC: forall
            i_src0 i_tgt0 w0 st_tgt0 st_src0
            k_src i_tgt
            st_src1
            (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
              (st_tgt0, i_tgt))
        (PGETSRC: forall
            i_src0 i_tgt0 w0 st_tgt0 st_src0
            k_src i_tgt
            (K: _sim_itree sim_itree RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
              (st_tgt0, i_tgt))
        (TAUTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt))
        (CHOOSETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: forall (x: X), <<SIMH: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Choose X) >>= k_tgt))
        (TAKETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: exists (x: X), <<SIM:_sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Take X) >>= k_tgt))
        (PPUTTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt i_src
            st_tgt1
            (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt))
        (PGETTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt i_src
            (K: _sim_itree sim_itree RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0)),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (PGet) >>= k_tgt))
        (PROGRESS: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0 i_src i_tgt
            (SIM: sim_itree _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (SRC: i_src0 = true)
            (TGT: i_tgt0 = true),
            P true true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      forall i_src0 i_tgt0 w0 st_src st_tgt
             (SIM: _sim_itree sim_itree RR i_src0 i_tgt0 w0 st_src st_tgt),
        P i_src0 i_tgt0 w0 st_src st_tgt.
  Proof.
    fix IH 6. i. inv SIM.
    { eapply RET; eauto. }
    { eapply CALL; eauto. }
    { eapply SYSCALL; eauto. }
    { eapply TAUSRC; eauto. }
    { eapply CHOOSESRC; eauto. des. esplits; eauto. }
    { eapply TAKESRC; eauto. }
    { eapply PPUTSRC; eauto. }
    { eapply PGETSRC; eauto. }
    { eapply TAUTGT; eauto. }
    { eapply CHOOSETGT; eauto. }
    { eapply TAKETGT; eauto. des. esplits; eauto. }
    { eapply PPUTTGT; eauto. }
    { eapply PGETTGT; eauto. }
    { eapply PROGRESS; eauto. }
  Qed.

  Definition sim_itree o_src o_tgt w0: relation _ :=
    paco8 _sim_itree bot8 _ _ (lift_rel w0 (@eq Any.t)) o_src o_tgt w0.

  Lemma sim_itree_mon: monotone8 _sim_itree.
  Proof.
    ii. induction IN using _sim_itree_ind2; try (by des; econs; ss; et).
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
    - econs; ss; et. ii. exploit K; et. i; des. esplits; et.
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree_mon: paco.
  Hint Resolve cpn8_wcompat: paco.

  Lemma sim_itree_ind
        R_src R_tgt (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        (P: bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        (RET: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            v_src v_tgt
            (RET: RR st_src0 st_tgt0 v_src v_tgt),
            P i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt)))
        (CALL: forall
            i_src0 i_tgt0 w w0 st_src0 st_tgt0
            fn varg k_src k_tgt
            (WF: wf w0 (st_src0, st_tgt0))
            (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
                paco8 _sim_itree bot8 _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret)),
            P i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
              (st_tgt0, trigger (Call fn varg) >>= k_tgt))
        (SYSCALL: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            fn varg rvs k_src k_tgt
            (K: forall vret,
                paco8 _sim_itree bot8 _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
              (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt))
        (TAUSRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt))
        (CHOOSESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: exists (x: X), <<SIM: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
              (st_tgt0, i_tgt))
        (TAKESRC: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X k_src i_tgt
            (K: forall (x: X), <<SIM: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>> /\ <<IH: P true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt)>>),
            P i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
              (st_tgt0, i_tgt))
        (PPUTSRC: forall
            i_src0 i_tgt0 w0 st_tgt0 st_src0
            k_src i_tgt
            st_src1
            (K: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
              (st_tgt0, i_tgt))
        (PGETSRC: forall
            i_src0 i_tgt0 w0 st_tgt0 st_src0
            k_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
            (IH: P true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
              (st_tgt0, i_tgt))
        (TAUTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt))
        (CHOOSETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: forall (x: X), <<SIMH: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Choose X) >>= k_tgt))
        (TAKETGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            X i_src k_tgt
            (K: exists (x: X), <<SIM:paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>> /\ <<IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x)>>),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (Take X) >>= k_tgt))
        (PPUTTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt i_src
            st_tgt1
            (K: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt)),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt))
        (PGETTGT: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0
            k_tgt i_src
            (K: paco8 _sim_itree bot8 _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
            (IH: P i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0)),
            P i_src0 i_tgt0 w0 (st_src0, i_src)
              (st_tgt0, trigger (PGet) >>= k_tgt))
        (PROGRESS: forall
            i_src0 i_tgt0 w0 st_src0 st_tgt0 i_src i_tgt
            (SIM: paco8 _sim_itree bot8 _ _ RR false false w0 (st_src0, i_src) (st_tgt0, i_tgt))
            (SRC: i_src0 = true)
            (TGT: i_tgt0 = true),
            P true true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      forall i_src0 i_tgt0 w0 st_src st_tgt
             (SIM: paco8 _sim_itree bot8 _ _ RR i_src0 i_tgt0 w0 st_src st_tgt),
        P i_src0 i_tgt0 w0 st_src st_tgt.
  Proof.
    i. punfold SIM. induction SIM using _sim_itree_ind2.
    { eapply RET; eauto. }
    { eapply CALL; eauto. i. exploit K; eauto. i. pclearbot. eauto. }
    { eapply SYSCALL; eauto. i. exploit K; eauto. i. pclearbot. eauto. }
    { eapply TAUSRC; eauto. }
    { eapply CHOOSESRC; eauto. des. esplits; eauto. }
    { eapply TAKESRC; eauto. i. exploit K; eauto. i. des.
      pclearbot. esplits; eauto. }
    { eapply PPUTSRC; eauto. }
    { eapply PGETSRC; eauto. }
    { eapply TAUTGT; eauto. }
    { eapply CHOOSETGT; eauto. i. exploit K; eauto. i. des.
      pclearbot. esplits; eauto. }
    { eapply TAKETGT; eauto. des. esplits; eauto. }
    { eapply PPUTTGT; eauto. }
    { eapply PGETTGT; eauto. }
    { eapply PROGRESS; eauto. pclearbot. auto. }
  Qed.

  Variant sim_itree_indC (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_indC_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | sim_itree_indC_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          sim_itree _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                     (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_indC_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          sim_itree _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                     (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itree_indC_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: sim_itree _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itree_indC_choose_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: exists (x: X), sim_itree _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                     (st_tgt0, i_tgt)
  | sim_itree_indC_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), sim_itree _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                     (st_tgt0, i_tgt)

  | sim_itree_indC_pput_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      st_src1
      (K: sim_itree _ _ RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                     (st_tgt0, i_tgt)

  | sim_itree_indC_pget_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      (K: sim_itree _ _ RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
                     (st_tgt0, i_tgt)


  | sim_itree_indC_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itree_indC_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itree_indC_take_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: exists (x: X), sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (Take X) >>= k_tgt)

  | sim_itree_indC_pput_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      st_tgt1
      (K: sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | sim_itree_indC_pget_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      (K: sim_itree _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
    :
      sim_itree_indC sim_itree RR i_src0 i_tgt0 w0 (st_src0, i_src)
                     (st_tgt0, trigger (PGet) >>= k_tgt)
  .

  Lemma sim_itree_indC_mon: monotone8 sim_itree_indC.
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
  Qed.
  Hint Resolve sim_itree_indC_mon: paco.

  Lemma sim_itree_indC_spec:
    sim_itree_indC <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit K; eauto. i. des.
      esplits; eauto. eapply rclo8_base. eauto. }
    { econs 3; eauto. i. eapply rclo8_base. eauto. }
    { econs 4; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 5; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 6; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 7; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 8; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 9; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 10; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 11; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 12; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 13; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
  Qed.

  Variant sim_itreeC (r g: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itreeC_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | sim_itreeC_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          g _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                 (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | sim_itreeC_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          g _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                 (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itreeC_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: r _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | sim_itreeC_choose_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: exists (x: X), r _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                 (st_tgt0, i_tgt)
  | sim_itreeC_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), r _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itreeC_pput_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      st_src1
      (K: r _ _ RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                 (st_tgt0, i_tgt)

  | sim_itreeC_pget_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      (K: r _ _ RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
                 (st_tgt0, i_tgt)


  | sim_itreeC_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | sim_itreeC_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Choose X) >>= k_tgt)
  | sim_itreeC_take_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: exists (x: X), r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (Take X) >>= k_tgt)

  | sim_itreeC_pput_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      st_tgt1
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | sim_itreeC_pget_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
    :
      sim_itreeC r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                 (st_tgt0, trigger (PGet) >>= k_tgt)
  .

  Lemma sim_itreeC_spec_aux:
    sim_itreeC <10= gpaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    i. inv PR.
    { gstep. econs 1; eauto. }
    { gstep. econs 2; eauto. i. gbase. eauto. }
    { gstep. econs 3; eauto. i. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 4; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 5; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 6; eauto. i. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 7; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 8; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 9; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 10; eauto. i. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 11; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 12; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 13; eauto. gbase. eauto. }
  Qed.

  Lemma sim_itreeC_spec r g
    :
      @sim_itreeC (gpaco8 (_sim_itree) (cpn8 _sim_itree) r g) (gpaco8 (_sim_itree) (cpn8 _sim_itree) g g)
      <8=
      gpaco8 (_sim_itree) (cpn8 _sim_itree) r g.
  Proof.
    i. eapply gpaco8_gpaco; [eauto with paco|].
    eapply gpaco8_mon.
    { eapply sim_itreeC_spec_aux. eauto. }
    { auto. }
    { i. eapply gupaco8_mon; eauto. }
  Qed.

  Lemma sim_itree_progress_flag R0 R1 RR r g w st_src st_tgt
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) g g R0 R1 RR false false w st_src st_tgt)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR true true w st_src st_tgt.
  Proof.
    gstep. destruct st_src, st_tgt. econs; eauto.
  Qed.

  Lemma sim_itree_flag_mon
        (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        R_src R_tgt (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        f_src0 f_tgt0 f_src1 f_tgt1 w st_src st_tgt
        (SIM: @_sim_itree sim_itree _ _ RR f_src0 f_tgt0 w st_src st_tgt)
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      @_sim_itree sim_itree _ _ RR f_src1 f_tgt1 w st_src st_tgt.
  Proof.
    revert f_src1 f_tgt1 SRC TGT.
    induction SIM using _sim_itree_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. des. esplits; eauto. }
    { econs 6; eauto. i. exploit K; eauto. i. des. eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. i. exploit K; eauto. i. des. eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { exploit SRC0; auto. exploit TGT0; auto. i. clarify. econs 14; eauto. }
  Qed.

  Definition sim_fsem: relation (Any.t -> itree Es Any.t) :=
    (eq ==> (fun it_src it_tgt => forall w mrs_src mrs_tgt (SIMMRS: wf w (mrs_src, mrs_tgt)),
                 sim_itree false false w (mrs_src, it_src)
                           (mrs_tgt, it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (Any.t -> itree Es Any.t)) := RelProd eq sim_fsem.


  Variant lflagC (r: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | lflagC_intro
      f_src0 f_src1 f_tgt0 f_tgt1 w st_src st_tgt
      (SIM: r _ _ RR f_src0 f_tgt0 w st_src st_tgt)
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      lflagC r RR f_src1 f_tgt1 w st_src st_tgt
  .

  Lemma lflagC_mon
        r1 r2
        (LE: r1 <8= r2)
    :
      @lflagC r1 <8= @lflagC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve lflagC_mon: paco.

  Lemma lflagC_spec: lflagC <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply GF in SIM.
    revert x3 x4 SRC TGT. induction SIM using _sim_itree_ind2; i; clarify.
    { econs 1; eauto. }
    { econs 2; eauto. i. exploit K; eauto. i. des.
      esplits; eauto. eapply rclo8_base. eauto. }
    { econs 3; eauto. i. eapply rclo8_base. eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. des. esplits; eauto. }
    { econs 6; eauto. i. exploit K; eauto. i. des. esplits; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. }
    { econs 10; eauto. i. exploit K; eauto. i. des. esplits; eauto. }
    { econs 11; eauto. des. esplits; eauto. }
    { econs 12; eauto. }
    { econs 13; eauto. }
    { exploit SRC0; auto. exploit TGT0; auto. i. clarify. econs 14; eauto.
      eapply rclo8_base; auto. }
  Qed.

  Lemma sim_itree_flag_down R0 R1 RR r g w st_src st_tgt f_src f_tgt
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR false false w st_src st_tgt)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR f_src f_tgt w st_src st_tgt.
  Proof.
    guclo lflagC_spec. econs; eauto.
  Qed.

  Lemma sim_itree_bot_flag_up R0 R1 RR w st_src st_tgt f_src f_tgt
        (SIM: paco8 _sim_itree bot8 R0 R1 RR true true w st_src st_tgt)
    :
      paco8 _sim_itree bot8 R0 R1 RR f_src f_tgt w st_src st_tgt.
  Proof.
    ginit. remember true in SIM at 1. remember true in SIM at 1.
    clear Heqb Heqb0. revert w st_src st_tgt f_src f_tgt b b0 SIM.
    gcofix CIH. i. revert f_src f_tgt.

    (* TODO: why induction using sim_itree_ind doesn't work? *)
    pattern b, b0, w, st_src, st_tgt.
    match goal with
    | |- ?P b b0 w st_src st_tgt => set P
    end.
    revert b b0 w st_src st_tgt SIM.
    eapply (@sim_itree_ind R0 R1 RR P); subst P; ss; i; clarify.
    { guclo sim_itree_indC_spec. econs 1; eauto. }
    { gstep. econs 2; eauto. i. gbase. eapply CIH; eauto. }
    { gstep. econs 3; eauto. i. gbase. eapply CIH; eauto. }
    { guclo sim_itree_indC_spec. econs 4; eauto. }
    { guclo sim_itree_indC_spec. econs 5; eauto. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 6; eauto. i. hexploit K; eauto. i. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 7; eauto. }
    { guclo sim_itree_indC_spec. econs 8; eauto. }
    { guclo sim_itree_indC_spec. econs 9; eauto. }
    { guclo sim_itree_indC_spec. econs 10; eauto. i. hexploit K; eauto. i. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 11; eauto. des. esplits; eauto. }
    { guclo sim_itree_indC_spec. econs 12; eauto. }
    { guclo sim_itree_indC_spec. econs 13; eauto. }
    { eapply sim_itree_flag_down. gfinal. right.
      eapply paco8_mon; eauto. ss.
    }
  Qed.

  Variant lbindR (r s: forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), bool -> bool -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop):
    forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), bool -> bool -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop :=
  | lbindR_intro
      f_src f_tgt w0 w1

      R_src R_tgt RR
      (st_src0 st_tgt0: st_local)
      (i_src: itree Es R_src) (i_tgt: itree Es R_tgt)
      (SIM: r _ _ RR f_src f_tgt w0 (st_src0, i_src) (st_tgt0, i_tgt))

      S_src S_tgt SS
      (k_src: ktree Es R_src S_src) (k_tgt: ktree Es R_tgt S_tgt)
      (SIMK: forall st_src1 st_tgt1 vret_src vret_tgt (SIM: RR st_src1 st_tgt1 vret_src vret_tgt), s _ _ SS false false w1 (st_src1, k_src vret_src) (st_tgt1, k_tgt vret_tgt))
    :
      lbindR r s SS f_src f_tgt w1 (st_src0, ITree.bind i_src k_src) (st_tgt0, ITree.bind i_tgt k_tgt)
  .

  Hint Constructors lbindR: core.

  Lemma lbindR_mon
        r1 r2 s1 s2
        (LEr: r1 <8= r2) (LEs: s1 <8= s2)
    :
      lbindR r1 s1 <8= lbindR r2 s2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Definition lbindC r := lbindR r r.
  Hint Unfold lbindC: core.

  Lemma lbindC_wrespectful: wrespectful8 (_sim_itree) lbindC.
  Proof.
    econs.
    { ii. eapply lbindR_mon; eauto. }
    i. rename l into llll. inv PR; csc.
    remember (st_src0, i_src). remember(st_tgt0, i_tgt).
    revert st_src0 i_src st_tgt0 i_tgt Heqp Heqp0.
    revert k_src k_tgt SIMK. eapply GF in SIM.
    induction SIM using _sim_itree_ind2; i; clarify.
    + rewrite ! bind_ret_l. exploit SIMK; eauto. i.
      eapply sim_itree_flag_mon.
      { eapply sim_itree_mon; eauto. i. eapply rclo8_base. auto. }
      { ss. }
      { ss. }
    + rewrite ! bind_bind. econs; eauto. i.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. i.
      eapply rclo8_clo_base. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto. i. exploit K; eauto. i. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
    + rewrite ! bind_tau. econs; eauto.
    + rewrite ! bind_bind. econs; eauto. i. exploit K; eauto. i. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto. des. esplits; eauto.
    + rewrite ! bind_bind. econs; eauto.
    + rewrite ! bind_bind. econs; eauto.
    + econs; eauto. eapply rclo8_clo_base. econs; eauto.
  Qed.

  Lemma lbindC_spec: lbindC <9= gupaco8 (_sim_itree) (cpn8 (_sim_itree)).
  Proof.
    intros. eapply wrespect8_uclo; eauto with paco. eapply lbindC_wrespectful.
  Qed.

End SIM.
Hint Resolve sim_itree_mon: paco.
Hint Resolve cpn8_wcompat: paco.

Lemma self_sim_itree:
  forall st itr,
    sim_itree (fun _ '(src, tgt) => src = tgt) top2 false false tt (st, itr) (st, itr).
Proof.
  ginit. gcofix CIH. i. ides itr.
  { gstep. eapply sim_itree_ret; ss. }
  { guclo sim_itree_indC_spec. econs.
    guclo sim_itree_indC_spec. econs.
    eapply sim_itree_progress_flag. gbase. auto.
  }
  destruct e.
  { dependent destruction c. rewrite <- ! bind_trigger. gstep.
    eapply sim_itree_call; ss. ii. subst.
    eapply sim_itree_flag_down. gbase. auto.
  }
  destruct s.
  { rewrite <- ! bind_trigger. resub. dependent destruction p.
    { guclo sim_itree_indC_spec. econs.
      guclo sim_itree_indC_spec. econs.
      eapply sim_itree_progress_flag. gbase. auto.
    }
    { guclo sim_itree_indC_spec. econs.
      guclo sim_itree_indC_spec. econs.
      eapply sim_itree_progress_flag. gbase. auto.
    }
  }
  { rewrite <- ! bind_trigger. resub. dependent destruction e.
    { guclo sim_itree_indC_spec. econs 10. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs 6. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs. i.
      eapply sim_itree_progress_flag. gbase. auto.
    }
  }
Qed.



(*** desiderata: (1) state-aware simulation relation !!!! ***)
(*** (2) not whole function frame, just my function frame !!!! ***)
(*** (3) would be great if induction tactic works !!!! (study itree case study more) ***)



Module ModSemPair.
Section SIMMODSEM.

  Variable (ms_src ms_tgt: ModSem.t).

  Let W: Type := (Any.t) * (Any.t).
  Inductive sim: Prop := mk {
    world: Type;
    wf: world -> W -> Prop;
    le: world -> world -> Prop;
    le_PreOrder: PreOrder le;
    sim_fnsems: Forall2 (sim_fnsem wf le) ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems);
    sim_initial: exists w_init, wf w_init (ms_src.(ModSem.initial_st), ms_tgt.(ModSem.initial_st));
  }.

End SIMMODSEM.

Lemma self_sim (ms: ModSem.t):
  sim ms ms.
Proof.
  econs; et.
  - instantiate (1:=fun (_ _: unit) => True). ss.
  - instantiate (1:=(fun (_: unit) '(src, tgt) => src = tgt)). (* fun p => fst p = snd p *)
    generalize (ModSem.fnsems ms).
    induction a; ii; ss.
    econs; eauto. econs; ss. ii; clarify.
    destruct w. exploit self_sim_itree; et.
  - ss.
Unshelve.
all: try (exact 0).
Qed.

Require Import Red IRed.
Ltac ired_l := try (prw _red_gen 2 1 0).
Ltac ired_r := try (prw _red_gen 1 1 0).
Ltac ired_both := ired_l; ired_r.
Lemma compose_aux_left:
  forall
  world0 (wf0: world0 -> Any.t * Any.t -> Prop) (le0: world0 -> world0 -> Prop) (le_PreOrder0: PreOrder le0)
  world1 (wf1: world1 -> Any.t * Any.t -> Prop) (le1: world1 -> world1 -> Prop) (le_PreOrder1: PreOrder le1)
  ,
    let le_both := fun '(u0, w0) '(u1, w1) => le0 u0 u1 /\ le1 w0 w1 in
    let wf_both := fun '(u0, w0) '(lrs0, lrt0) =>
                     exists ls0 rs0 lt0 rt0 : Any.t,
                       lrs0 = Any.pair ls0 rs0 /\ lrt0 = Any.pair lt0 rt0 /\ wf0 u0 (ls0, lt0) /\ wf1 w0 (rs0, rt0) in
    forall
      (le_both_PreOrder: PreOrder le_both)
      (sems semt: itree _ _) wl0 wr_begin wr0 sl0 sr0 tl0 tr0 fs ft
      (LE: le1 wr_begin wr0)
      (WF: wf1 wr0 (sr0, tr0))
      (SIM: sim_itree wf0 le0 fs ft wl0 (sl0, sems) (tl0, semt))
    ,
      sim_itree wf_both le_both fs ft (wl0, wr_begin) (Any.pair sl0 sr0, focus_left sems) (Any.pair tl0 tr0, focus_left semt)
.
Proof.
  ii. ginit. revert_until le_both_PreOrder. gcofix CIH.
  i.
  punfold SIM.
  remember (lift_rel wf0 le0 wl0 eq) as tmp.
  remember (sl0, sems) as tmp0.
  remember (tl0, semt) as tmp1.
  revert Heqtmp. revert Heqtmp0. revert Heqtmp1.
  revert semt. revert sems. revert tl0. revert sl0.
  induction SIM using _sim_itree_ind2; i; clarify; simpl_depind; ired_both.
  - gstep. econs 1; eauto. rr. rr in RET. des. subst. esplits; et.
    { instantiate (1:=(_, _)). ss. esplits; et. }
    { rr. esplits; et. }
  - gstep. rename w0 into wl0. rename w into wl1. econs 2; eauto.
    { instantiate (1:=(_, _)). ss. esplits; et. }
    i. ss. des_ifs. des. ss. des. subst. exploit K; et. intro T; des. pclearbot.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; [|et|et].
    { etrans; et. }
  - gstep. econs 3; eauto.
    i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; et.
    specialize (K vret); pclearbot. et.

  - guclo sim_itree_indC_spec. econs 4; eauto.
  - guclo sim_itree_indC_spec. des. econs 5; eauto. esplits; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both. eauto.
  - guclo sim_itree_indC_spec. econs 6; eauto. i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    spc K. des. eapply IH; et.
  - guclo sim_itree_indC_spec. econs; eauto. ired_both.
    guclo sim_itree_indC_spec. econs 7; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    eauto.
  - guclo sim_itree_indC_spec. econs 8; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    eauto.

  - guclo sim_itree_indC_spec. econs 9; eauto.
  - guclo sim_itree_indC_spec. econs 10; eauto. i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    spc K. des. eapply IH; et.
  - guclo sim_itree_indC_spec. des. econs 11; eauto. esplits; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both. eauto.
  - guclo sim_itree_indC_spec. econs; eauto. ired_both.
    guclo sim_itree_indC_spec. econs 12; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    eauto.
  - guclo sim_itree_indC_spec. econs 13; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    eauto.

  - pclearbot. gstep. econs 14; eauto. gbase. eapply CIH; et.
Qed.

Lemma compose_aux_right:
  forall
  world0 (wf0: world0 -> Any.t * Any.t -> Prop) (le0: world0 -> world0 -> Prop) (le_PreOrder0: PreOrder le0)
  world1 (wf1: world1 -> Any.t * Any.t -> Prop) (le1: world1 -> world1 -> Prop) (le_PreOrder1: PreOrder le1)
  ,
    let le_both := fun '(u0, w0) '(u1, w1) => le0 u0 u1 /\ le1 w0 w1 in
    let wf_both := fun '(u0, w0) '(lrs0, lrt0) =>
                     exists ls0 rs0 lt0 rt0 : Any.t,
                       lrs0 = Any.pair ls0 rs0 /\ lrt0 = Any.pair lt0 rt0 /\ wf0 u0 (ls0, lt0) /\ wf1 w0 (rs0, rt0) in
    forall
      (le_both_PreOrder: PreOrder le_both)
      (sems semt: itree _ _) wl0 wl_begin wr0 sl0 sr0 tl0 tr0 fs ft
      (LE: le0 wl_begin wl0)
      (WF: wf0 wl0 (sl0, tl0))
      (SIM: sim_itree wf1 le1 fs ft wr0 (sr0, sems) (tr0, semt))
    ,
      sim_itree wf_both le_both fs ft (wl_begin, wr0) (Any.pair sl0 sr0, focus_right sems) (Any.pair tl0 tr0, focus_right semt)
.
Proof.
  ii. ginit. revert_until le_both_PreOrder. gcofix CIH.
  i.
  punfold SIM.
  remember (lift_rel wf1 le1 wr0 eq) as tmp.
  remember (sr0, sems) as tmp0.
  remember (tr0, semt) as tmp1.
  revert Heqtmp. revert Heqtmp0. revert Heqtmp1.
  revert semt. revert sems. revert tr0. revert sr0.
  induction SIM using _sim_itree_ind2; i; clarify; simpl_depind; ired_both.
  - gstep. econs 1; eauto. rr. rr in RET. des. subst. esplits; et.
    { instantiate (1:=(_, _)). ss. esplits; et. }
    { rr. esplits; et. }
  - gstep. rename w0 into wr0. rename w into wr1. econs 2; eauto.
    { instantiate (1:=(_, _)). ss. esplits; et. }
    i. ss. des_ifs. des. ss. des. subst. exploit K; et. intro T; des. pclearbot.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; [|et|et].
    { etrans; et. }
  - gstep. econs 3; eauto.
    i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    gbase. eapply CIH; et.
    specialize (K vret); pclearbot. et.

  - guclo sim_itree_indC_spec. econs 4; eauto.
  - guclo sim_itree_indC_spec. des. econs 5; eauto. esplits; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both. eauto.
  - guclo sim_itree_indC_spec. econs 6; eauto. i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    spc K. des. eapply IH; et.
  - guclo sim_itree_indC_spec. econs; eauto. ired_both.
    guclo sim_itree_indC_spec. econs 7; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    eauto.
  - guclo sim_itree_indC_spec. econs 8; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    eauto.

  - guclo sim_itree_indC_spec. econs 9; eauto.
  - guclo sim_itree_indC_spec. econs 10; eauto. i.
    ired_both. guclo sim_itree_indC_spec. econs; eauto. ired_both.
    spc K. des. eapply IH; et.
  - guclo sim_itree_indC_spec. des. econs 11; eauto. esplits; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both. eauto.
  - guclo sim_itree_indC_spec. econs; eauto. ired_both.
    guclo sim_itree_indC_spec. econs 12; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    eauto.
  - guclo sim_itree_indC_spec. econs 13; eauto. ired_both.
    guclo sim_itree_indC_spec. econs; eauto. ired_both.
    eauto.

  - pclearbot. gstep. econs 14; eauto. gbase. eapply CIH; et.
Qed.



Theorem compose
  md_src0 md_tgt0 md_src1 md_tgt1
  (SIM0: sim md_src0 md_tgt0)
  (SIM1: sim md_src1 md_tgt1)
  :
  <<SIM: sim (md_src0 ⊕ md_src1) (md_tgt0 ⊕ md_tgt1)>>
.
Proof.
  inv SIM0. des.
  inv SIM1. des.
  set(le_both := (fun '(u0, w0) '(u1, w1) => le u0 u1 /\ le0 w0 w1): (world * world0) -> (world * world0) -> Prop).
  set(wf_both := (fun '(u0, w0) '(lrs0, lrt0) => exists ls0 rs0 lt0 rt0, lrs0 = Any.pair ls0 rs0 /\ lrt0 = Any.pair lt0 rt0 /\
                                                                           wf u0 (ls0, lt0) /\ wf0 w0 (rs0, rt0))).
  assert(LEBOTH: PreOrder le_both).
  { econs; et.
    - ii. rr. des_ifs; split; try refl.
    - ii. rr. des_ifs; ss. des_ifs. des; ss. des. split; try etrans; et.
  }
  econs; et.
  2: { instantiate (1:=wf_both). esplits ;ss. r. instantiate (1:=(w_init, w_init0)). ss. esplits; ss. }
  eapply Forall2_app.
  - eapply Forall2_apply_Forall2; et.
    ii. destruct a, b; ss. rr in H. rr. unfold RelCompFun in *. ss. des. subst. esplits; ss.
    do 2 r in H0. do 2 r.
    ii. subst. destruct w; ss. des; subst. eapply compose_aux_left; ss; et. refl.
  - eapply Forall2_apply_Forall2; et.
    ii. destruct a, b; ss. rr in H. rr. unfold RelCompFun in *. ss. des. subst. esplits; ss.
    do 2 r in H0. do 2 r.
    ii. subst. destruct w; ss. des; subst. eapply compose_aux_right; ss; et. refl.
Qed.

Require Import SimGlobal.

Module TAC.
  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac step := ired_both; guclo simg_safe_spec; econs; et; i.
  Ltac steps := (repeat step); ired_both.

  Ltac force := ired_both; guclo simg_indC_spec; econs; et.
End TAC.
Import TAC.

Lemma Forall2_alist_find
        X kxs0 kxs1
        sim
        (SIM: Forall2 ((@eq string) * sim)%signature kxs0 kxs1)
        (k: string) (x0: X)
        (FIND: alist_find k kxs0 = Some x0)
  :
  <<FIND: exists (x1: X), alist_find k kxs1 = Some x1 /\ sim x0 x1>>
.
Proof.
  induction SIM; ii; ss.
  des_ifs; ss; unfold rel_dec in *; ss; des_sumbool; subst; rr in H; des; unfold RelCompFun in *; ss; subst; et; ss.
Qed.

Lemma adequacy_aux
  (world: Type)
  (wf: world -> Any.t * Any.t -> Prop)
  (le: world -> world -> Prop)
  `{PreOrder _ le}
  ms_src ms_tgt
  (SIM: Forall2 (sim_fnsem wf le) (ModSem.fnsems ms_src) (ModSem.fnsems ms_tgt))
  w0 st_src st_tgt
  itr_src itr_tgt
  f_src f_tgt
  (SIMF: sim_itree wf le f_src f_tgt w0 (st_src, itr_src) (st_tgt, itr_tgt))
  :
  paco7 _simg bot7 (p_state * Any.t)%type (p_state * Any.t)%type
    (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
       lift_rel wf le w0 (@eq Any.t) st_src st_tgt ret_src ret_tgt) f_src f_tgt
    (interp_Es (ModSem.prog ms_src) itr_src st_src)
    (interp_Es (ModSem.prog ms_tgt) itr_tgt st_tgt)
.
Proof.
  ginit.
  { i. eapply cpn7_wcompat; eauto with paco. }
  revert_until SIM.
  gcofix CIH. i.
  {
    rr in SIMF.
    remember (st_src, itr_src).
    remember (st_tgt, itr_tgt).
    remember w0 in SIMF at 2.
    revert st_src itr_src st_tgt itr_tgt Heqp Heqp0 Heqw.
    punfold SIMF. induction SIMF using _sim_itree_ind2; ss; i; clarify.
    - rr in RET. des. step. r. esplits; et.
    - destruct (alist_find fn (ModSem.fnsems ms_src)) eqn:SRC; cycle 1.
      { steps. rewrite SRC. unfold unwrapU, triggerUB. step. ss. }
      { hexploit (Forall2_alist_find SIM _ SRC); et. intro TGT. des.
        steps. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
        apply simg_progress_flag.
        guclo bindC_spec. econs.
        { gbase. eapply CIH. { instantiate (1:=w1). eauto. } }
        { i. ss. des_ifs. r in SIM0. des. subst.
          hexploit K; et. i. des. pclearbot.
          steps. gbase. eapply CIH; ss.
          eapply sim_itree_bot_flag_up. eauto.
        }
      }
    - step. i. subst. apply simg_progress_flag.
      hexploit (K x_tgt). i. des. pclearbot.
      steps. gbase. eapply CIH; et.
    - ired_both. steps.
    - des. force. exists x. steps. eapply IH; eauto.
    - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
    - steps. eapply IHSIMF; eauto.
    - steps. eapply IHSIMF; eauto.
    - steps.
    - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
    - des. force. exists x. steps. eapply IH; eauto.
    - steps. eapply IHSIMF; eauto.
    - steps. eapply IHSIMF; eauto.
    - eapply simg_progress_flag. gbase. eapply CIH; et.
      pclearbot. eauto.
  }
Qed.

Theorem adequacy
  `{EMSConfig}
  (P Q: Prop)
  ms_src ms_tgt
  (SIM: ModSemPair.sim ms_src ms_tgt)
  (WF: Q -> P)
  :
  (Beh.of_program (ModSem.compile ms_tgt (Some P)))
  <1=
    (Beh.of_program (ModSem.compile ms_src (Some Q))).
Proof.
  eapply adequacy_global_itree; ss.
  inv SIM.
  des. ginit.
  { eapply cpn7_wcompat; eauto with paco. }
  unfold ModSem.initial_itr, assume.
  steps.
  force. esplits; et. steps.
  unfold ITree.map. steps.
  destruct (alist_find "main" (ModSem.fnsems ms_src)) eqn:T; cycle 1.
  { cbn. unfold triggerUB. steps. ss. }
  hexploit (Forall2_alist_find sim_fnsems _ T); et. intro U. des.
  rename i into fs. rename x1 into ft.
  ss. steps. rewrite U. ss. steps.
  guclo bindC_spec. econs.
  { eapply simg_progress_flag. gfinal. right. eapply adequacy_aux; et. }
  { i. des_ifs. r in SIM. des; clarify. steps. }
Qed.

End ModSemPair.








Module ModPair.
Section SIMMOD.
  Context `{LD: Sk.ld}.
  Variable (md_src md_tgt: Mod.t).
  Inductive sim: Prop := mk {
    sim_modsem:
      forall sk
             (SKINCL: Sk.extends md_tgt.(Mod.sk) sk)
             (SKWF: Sk.wf sk),
        <<SIM: ModSemPair.sim (md_src.(Mod.get_modsem) sk) (md_tgt.(Mod.get_modsem) sk)>>;
    sim_sk: forall (SKWF: Sk.wf md_src.(Mod.sk)), md_src.(Mod.sk) ≡ md_tgt.(Mod.sk);
  }.

End SIMMOD.

Section FACTS.

Context `{LD: Sk.ld}.

Theorem compose
  md_src0 md_tgt0 md_src1 md_tgt1
  (SIM0: ModPair.sim md_src0 md_tgt0)
  (SIM1: ModPair.sim md_src1 md_tgt1)
  :
  <<SIM: ModPair.sim (md_src0 ⊕ md_src1) (md_tgt0 ⊕ md_tgt1)>>
.
Proof.
  inv SIM0.
  inv SIM1.
  des.
  econs; ss.
  2:{ i. rewrite sim_sk0.
      2: { eapply Sk.wf_mon; et. r. esplits; et. refl. }
      rewrite sim_sk1.
      2: { eapply Sk.wf_mon; et. r. esplits; et. rewrite Sk.add_comm. refl. }
      refl.
  }
  ii; ss.
  eapply ModSemPair.compose; et.
  - eapply sim_modsem0; ss. etrans; et. r. esplits; et. refl.
  - eapply sim_modsem; ss. etrans; et. r. esplits; et. rewrite Sk.add_comm. refl.
Qed.

Theorem adequacy
  md_src md_tgt
  (SIM: ModPair.sim md_src md_tgt)
  :
  md_tgt ⊑ md_src
.
Proof.
  ii. unfold Mod.compile, Mod.enclose in *.
  destruct (classic (Mod.wf (ctx ⊕ md_src))).
  2:{ eapply ModSem.compile_not_wf. ss. }
  pose (sk_tgt := (Mod.sk (ctx ⊕ md_tgt))).
  pose (sk_src := (Mod.sk (ctx ⊕ md_src))).
  destruct (classic (Sk.wf (Mod.sk md_src))); rename H0 into SKWF.
  2: { eapply ModSem.initial_itr_not_wf. intro T. eapply SKWF. inv T; ss. eapply Sk.wf_mon; et. r. esplits; et.
       rewrite Sk.add_comm; et. refl. }
  assert (SKEQ: sk_tgt ≡ sk_src).
  { unfold sk_src, sk_tgt. ss. inv SIM. spc sim_sk0. rewrite sim_sk0. refl. }

  rr in H. unfold Mod.enclose in *. fold sk_src in H. des. inv WF.
  rename wf_fnsems into FNWF.
  {
    folder.
    inv SIM. ss.
    exploit sim_modsem0.
    { instantiate (1:=sk_src).
      subst sk_src. r. esplits; et. rewrite Sk.add_comm. rewrite sim_sk0; ss. refl. }
    { eauto. }
    intro T.
    eapply ModSemPair.adequacy; revgoals; et.
    2: {
      eapply ModSemPair.compose; rewrite <- Mod.get_modsem_Proper; et.
      - eapply ModSemPair.self_sim.
      - eapply sim_modsem0; et.
        { r. subst sk_tgt. esplits. rewrite Sk.add_comm; refl. }
        rewrite SKEQ; ss.
    }
    { unfold Mod.wf, Mod.enclose. ii. ss. des; ss. folder. esplits; et.
      2: { rewrite SKEQ; ss. }
      {
        rewrite Mod.get_modsem_Proper; et.
        rewrite (Mod.get_modsem_Proper _ _ _ SKEQ); et.
        econs.
        match goal with
        | H: NoDup ?l0 |- NoDup ?l1 => replace l1 with l0
        end; auto. ss.
        rewrite ! List.map_app. f_equal. rewrite ! List.map_map.
        eapply Forall2_eq. inv T. eapply Forall2_apply_Forall2; et.
        i. destruct a, b. inv H. ss.
      }
    }
  }
Qed.

Corollary adequacy'
  `{EMSConfig}
  md_src md_tgt
  (SIM: ModPair.sim md_src md_tgt)
  :
  md_tgt ⊑ md_src
.
Proof.
  eapply adequacy; ss.
Qed.

End FACTS.
End ModPair.


