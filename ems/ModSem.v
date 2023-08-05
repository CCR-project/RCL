Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export ModSemE.
Export Events.
Require Export AList.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Permutation.

Set Implicit Arguments.




Require Import Red IRed.
Section AUX.

  Global Program Instance interp_Es_rdb: red_database (mk_box (@Events.interp_Es)) :=
    mk_rdb
      1
      (mk_box Events.interp_Es_bind)
      (mk_box Events.interp_Es_tau)
      (mk_box Events.interp_Es_ret)
      (mk_box Events.interp_Es_pE)
      (mk_box Events.interp_Es_pE)
      (mk_box Events.interp_Es_callE)
      (mk_box Events.interp_Es_eventE)
      (mk_box Events.interp_Es_triggerUB)
      (mk_box Events.interp_Es_triggerNB)
      (mk_box interp_Es_unwrapU)
      (mk_box interp_Es_unwrapN)
      (mk_box interp_Es_assume)
      (mk_box interp_Es_guarantee)
      (mk_box interp_Es_ext)
  .

  Global Program Instance focus_left_rdb: red_database (mk_box (@focus_left)) :=
    mk_rdb
      0
      (mk_box focus_left_bind)
      (mk_box focus_left_tau)
      (mk_box focus_left_ret)
      (mk_box focus_left_pE)
      (mk_box focus_left_pE)
      (mk_box focus_left_callE)
      (mk_box focus_left_eventE)
      (mk_box focus_left_triggerUB)
      (mk_box focus_left_triggerNB)
      (mk_box focus_left_unwrapU)
      (mk_box focus_left_unwrapN)
      (mk_box focus_left_assume)
      (mk_box focus_left_guarantee)
      (mk_box focus_left_ext)
  .

  Global Program Instance focus_right_rdb: red_database (mk_box (@focus_right)) :=
    mk_rdb
      0
      (mk_box focus_right_bind)
      (mk_box focus_right_tau)
      (mk_box focus_right_ret)
      (mk_box focus_right_pE)
      (mk_box focus_right_pE)
      (mk_box focus_right_callE)
      (mk_box focus_right_eventE)
      (mk_box focus_right_triggerUB)
      (mk_box focus_right_triggerNB)
      (mk_box focus_right_unwrapU)
      (mk_box focus_right_unwrapN)
      (mk_box focus_right_assume)
      (mk_box focus_right_guarantee)
      (mk_box focus_right_ext)
  .

  Global Program Instance core_rdb: red_database (mk_box (@core)) :=
    mk_rdb
      0
      (mk_box core_bind)
      (mk_box core_tau)
      (mk_box core_ret)
      (mk_box core_pE)
      (mk_box core_pE)
      (mk_box core_callE)
      (mk_box core_eventE)
      (mk_box core_triggerUB)
      (mk_box core_triggerNB)
      (mk_box core_unwrapU)
      (mk_box core_unwrapN)
      (mk_box core_assume)
      (mk_box core_guarantee)
      (mk_box core_ext)
  .

End AUX.

Theorem core_idemp {R}: forall (itr: itree _ R), | | itr | | ≈ | itr | .
Proof.
  i.
  unfold bar, itree_Bar, core.
  rewrite interp_interp.
  eapply eutt_interp; try refl.
  ii.
  destruct a; ss.
  { cbn. unfold trivial_Handler. rewrite interp_trigger. grind. resub. setoid_rewrite tau_eutt. grind. refl. }
  destruct s; ss.
  { cbn. unfold trivial_Handler. destruct p; ss.
    - rewrite interp_trigger. grind. setoid_rewrite tau_eutt. grind. refl.
    - unfold triggerUB. grind. rewrite ! interp_trigger. grind. resub. f_equiv; ss. refl.
  }
  { cbn. unfold trivial_Handler. rewrite interp_trigger. grind. resub. setoid_rewrite tau_eutt. grind. refl. }
Qed.













Class EMSConfig := { finalize: Any.t -> option Any.t; initial_arg: Any.t }.



Module ModSem.
Section MODSEM.


  (* Record t: Type := mk { *)
  (*   state: Type; *)
  (*   local_data: Type; *)
  (*   step (skenv: SkEnv.t) (st0: state) (ev: option event) (st1: state): Prop; *)
  (*   state_sort: state -> sort; *)
  (*   initial_local_data: local_data; *)
  (*   sk: Sk.t; *)
  (*   name: string; *)
  (* } *)
  (* . *)

  Record t: Type := mk {
    (* initial_ld: mname -> GRA; *)
    fnsems: alist gname (Any.t -> itree Es Any.t);
    initial_st: Any.t;
  }
  .

  Global Instance equiv: Equiv t :=
    fun ms0 ms1 => Forall2 (fun '(fn0, ktr0) '(fn1, ktr1) => fn0 = fn1 /\ (forall x, ktr0 x ≈ ktr1 x)) ms0.(fnsems) ms1.(fnsems)
                   /\ ms0.(initial_st) = ms1.(initial_st).

  Global Program Instance equiv_Equivalence: Equivalence equiv.
  Next Obligation.
    ii. r. esplits; ss. eapply Forall2_impl. 2: { eapply Forall2_eq; ss. } i; ss. des_ifs. esplits; ss. refl.
  Qed.
  Next Obligation.
    ii. r in H. r. des. split; ss. eapply Forall2_sym; et. eapply Forall2_impl; [|et].
    ii; ss. des_ifs. des; subst; ss. rr. esplits; ss. sym; ss.
  Qed.
  Next Obligation.
    ii. rr in H. rr in H0. des; subst.
    rr. esplits; et.
    2: { etrans; et. }
    eapply Forall2_impl.
    2:{ eapply Forall2_trans; et. }
    ss. ii. des. des_ifs. des; subst. esplits; ss. etrans; et.
  Qed.

  Definition core (ms: t): t :=
    mk (List.map (map_snd bar) ms.(fnsems)) ms.(initial_st)
  .

  Global Program Instance bar: Bar t := core.

  Record wf (ms: t): Prop := mk_wf {
    (* wf_fnsems: NoDup (List.map fst ms.(fnsems)); *)
  }
  .

  (* Global Program Instance equiv: Equiv t := *)
  (*   fun ms0 ms1 => <<ST: ms0.(initial_st) = ms1.(initial_st)>> /\ <<SEM: Permutation ms0.(fnsems) ms1.(fnsems)>> *)
  (* . *)

  (* Global Program Instance equiv_Equivalence: Equivalence ((≡)). *)
  (* Next Obligation. *)
  (*   ii. rr. esplits; et. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   ii. rr. rr in H. des. esplits; et. sym; et. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   ii. rr. rr in H. rr in H0. des. esplits; ss; etrans; et. *)
  (* Qed. *)

  (* Global Program Instance wf_Proper: Proper ((≡) ==> impl) wf. *)
  (* Next Obligation. *)
  (*   ii; ss. *)
  (* Qed. *)



  (*** using "Program Definition" makes the definition uncompilable; why?? ***)
  Definition add (ms0 ms1: t): t := {|
    (* sk := Sk.add md0.(sk) md1.(sk); *)
    (* initial_ld := URA.add (t:=URA.pointwise _ _) md0.(initial_ld) md1.(initial_ld); *)
    (* sem := fun _ '(Call fn args) => *)
    (*          (if List.in_dec string_dec fn md0.(sk) then md0.(sem) else md1.(sem)) _ (Call fn args); *)
    fnsems := app (List.map (map_snd (fun ktr => (@focus_left _) ∘ ktr)) ms0.(fnsems))
                  (List.map (map_snd (fun ktr => (@focus_right _) ∘ ktr)) ms1.(fnsems));
    initial_st := Any.pair ms0.(initial_st) ms1.(initial_st);
  |}
  .

  Global Program Instance add_OPlus: OPlus t := add.

  (* Global Program Instance add_Proper: Proper ((≡) ==> (≡) ==> (≡)) ((⊕)). *)
  (* Next Obligation. *)
  (*   ii. rr in H. rr in H0. des. rr. esplits; et. *)
  (*   - ss. f_equal; et. *)
  (*   - ss. rewrite Permutation_app; et. *)
  (*     + rewrite Permutation_map; et. *)
  (*     + rewrite Permutation_map; et. *)
  (* Qed. *)


  Section INTERP.

  Variable ms: t.

  (* Definition prog: callE ~> itree Es := *)
  (*   fun _ '(Call fn args) => *)
  (*     sem <- (alist_find fn ms.(fnsems))?;; *)
  (*     rv <- (sem args);; *)
  (*     Ret rv *)
  (* . *)

  Definition prog: callE ~> itree Es :=
    fun _ '(Call fn args) =>
      n <- trigger (Take _);;
      assume(exists sem, nth_error ms.(fnsems) n = Some (fn, sem));;;
      '(_, sem) <- (nth_error ms.(fnsems) n)?;;
      rv <- (sem args);;
      Ret rv
  .



  Definition initial_p_state: p_state := ms.(initial_st).

  Context `{CONF: EMSConfig}.
  Definition initial_itr (P: option Prop): itree (eventE) Any.t :=
    match P with
    | None => Ret tt
    | Some P' => guarantee (<<WF: P'>>)
    end;;;
    snd <$> interp_Es prog (prog (Call "main" initial_arg)) (initial_p_state).



  Let state: Type := itree eventE Any.t.

  Definition state_sort (st0: state): sort :=
    match (observe st0) with
    | TauF _ => demonic
    | RetF rv =>
      match (finalize rv) with
      | Some rv => final rv
      | _ => angelic
      end
    | VisF (Choose X) k => demonic
    | VisF (Take X) k => angelic
    | VisF (Syscall fn args rvs) k => vis
    end
  .

  Inductive step: state -> option event -> state -> Prop :=
  | step_tau
      itr
    :
      step (Tau itr) None itr
  | step_choose
      X k (x: X)
    :
      step (Vis (subevent _ (Choose X)) k) None (k x)
  | step_take
      X k (x: X)
    :
      step (Vis (subevent _ (Take X)) k) None (k x)
  | step_syscall
      fn args rv (rvs: Any.t -> Prop) k
      (SYSCALL: syscall_sem (event_sys fn args rv))
      (RETURN: rvs rv)
    :
      step (Vis (subevent _ (Syscall fn args rvs)) k) (Some (event_sys fn args rv)) (k rv)
  .

  Lemma step_trigger_choose_iff X k itr e
        (STEP: step (trigger (Choose X) >>= k) e itr)
    :
      exists x,
        e = None /\ itr = k x.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et.  }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
  Qed.

  Lemma step_trigger_take_iff X k itr e
        (STEP: step (trigger (Take X) >>= k) e itr)
    :
      exists x,
        e = None /\ itr = k x.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et.  }
    { eapply f_equal with (f:=observe) in H0. ss. }
  Qed.

  Lemma step_tau_iff itr0 itr1 e
        (STEP: step (Tau itr0) e itr1)
    :
      e = None /\ itr0 = itr1.
  Proof.
    inv STEP. et.
  Qed.

  Lemma step_ret_iff rv itr e
        (STEP: step (Ret rv) e itr)
    :
      False.
  Proof.
    inv STEP.
  Qed.

  Lemma step_trigger_syscall_iff fn args rvs k e itr
        (STEP: step (trigger (Syscall fn args rvs) >>= k) e itr)
    :
      exists rv, itr = k rv /\ e = Some (event_sys fn args rv)
                 /\ <<RV: rvs rv>> /\ <<SYS: syscall_sem (event_sys fn args rv)>>.
  Proof.
    inv STEP.
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss. }
    { eapply f_equal with (f:=observe) in H0. ss.
      unfold trigger in H0. ss. cbn in H0.
      dependent destruction H0. ired. et. }
  Qed.


  Let itree_eta E R (itr0 itr1: itree E R)
      (OBSERVE: observe itr0 = observe itr1)
    :
      itr0 = itr1.
  Proof.
    rewrite (itree_eta_ itr0).
    rewrite (itree_eta_ itr1).
    rewrite OBSERVE. auto.
  Qed.

  Lemma step_trigger_choose X k x
    :
      step (trigger (Choose X) >>= k) None (k x).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Choose X) k)
    end; ss.
    { econs. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.

  Lemma step_trigger_take X k x
    :
      step (trigger (Take X) >>= k) None (k x).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Take X) k)
    end; ss.
    { econs. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.

  Lemma step_trigger_syscall fn args (rvs: Any.t -> Prop) k rv
        (RV: rvs rv) (SYS: syscall_sem (event_sys fn args rv))
    :
      step (trigger (Syscall fn args rvs) >>= k) (Some (event_sys fn args rv)) (k rv).
  Proof.
    unfold trigger. ss.
    match goal with
    | [ |- step ?itr _ _] =>
      replace itr with (Subevent.vis (Syscall fn args rvs) k)
    end; ss.
    { econs; et. }
    { eapply itree_eta. ss. cbv. f_equal.
      extensionality x0. eapply itree_eta. ss. }
  Qed.


  Program Definition compile_itree: itree eventE Any.t -> semantics :=
    fun itr =>
      {|
        STS.state := state;
        STS.step := step;
        STS.initial_state := itr;
        STS.state_sort := state_sort;
      |}
  .
  Next Obligation. inv STEP; inv STEP0; ss. csc. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.
  Next Obligation. inv STEP; ss. Qed.

  Definition compile P: semantics :=
    compile_itree (initial_itr P).

  (* Program Definition interp_no_forge: semantics := {| *)
  (*   STS.state := state; *)
  (*   STS.step := step; *)
  (*   STS.initial_state := itr2'; *)
  (*   STS.state_sort := state_sort; *)
  (* |} *)
  (* . *)
  (* Next Obligation. inv STEP; inv STEP0; ss. csc. rewrite SYSCALL in *. csc. Qed. *)
  (* Next Obligation. inv STEP; ss. Qed. *)
  (* Next Obligation. inv STEP; ss. Qed. *)

  Lemma initial_itr_not_wf P
        (WF: ~ P)
        tr
        (BEH: Beh.of_program (compile_itree (initial_itr (Some P))) tr)
    :
      tr = Tr.nb.
  Proof.
    punfold BEH. inv BEH; ss.
    - punfold SPIN. inv SPIN; ss. des; ss. unfold initial_itr in STEP0. unfold guarantee in *. inv STEP0; ss; csc.
      { irw in H0; csc. }
      { irw in H0; csc. }
      { irw in H0; csc. }
      { rewrite <- bind_trigger in H0. irw in H0. simpl_depind. }
    - inv STEP. des. subst; ss. unfold initial_itr, guarantee in STEP. inv STEP; ss; csc.
      { irw in H0; csc. }
      { irw in H0; csc. }
      { irw in H0; csc. }
  Qed.

  Lemma compile_not_wf P
        (WF: ~ P)
        tr
        (BEH: Beh.of_program (compile (Some P)) tr)
    :
      tr = Tr.nb.
  Proof.
    eapply initial_itr_not_wf; et.
  Qed.

  End INTERP.

  Definition cref (ms_tgt ms_src: t): Prop :=
    forall `{EMSConfig} P (ctx: t), Beh.of_program (compile (ctx ⊕ ms_tgt) P) <1= Beh.of_program (compile (ctx ⊕ ms_src) P)
  .

  Global Program Instance cref_Ref: Ref t := cref.

  Global Program Instance equiv_facts: EquivFacts.
  Global Program Instance bar_facts: BarFacts.
  Next Obligation.
    i.
    unfold Coqlib.bar, bar, core.
    ss. rr. esplits; ss.
    rewrite ! List.map_map.
    eapply Forall2_apply_Forall2.
    { refl. }
    ii; ss. subst. des_ifs. destruct b; ss. clarify.
    esplits; ss. ii. eapply core_idemp.
  Qed.
  Next Obligation.
    rr. esplits; ss.
    rewrite ! List.map_map. rewrite ! map_app.
    eapply Forall2_app.
    - rewrite ! List.map_map.
      eapply Forall2_apply_Forall2; [refl|]. ii; ss. subst. des_ifs. destruct b0; ss. clarify. esplits; ss.
      ii. unfold focus_left, Coqlib.bar, ktree_Bar, Coqlib.bar, itree_Bar, Events.core.
      rewrite ! interp_interp. eapply eutt_interp; try refl. ii.
      unfold trivial_Handler.
      destruct a0; cbn.
      { rewrite ! interp_trigger. grind. resub. refl. }
      destruct s0; cbn.
      { destruct p; ss.
        - rewrite ! interp_trigger. grind. rewrite ! interp_trigger. grind.
          unfold triggerUB. grind.
          resub. refl. }
      ss.
    ii.
    ss.
  Qed.

  Global Program Instance refines_Proper: @Proper (t -> t -> Prop) ((≡) ==> (≡) ==> impl) (⊑).
  Next Obligation.
    ii.
    admit "should hold".
  Qed.

End MODSEM.
End ModSem.
















(* Module Events. *)
Section EVENTSCOMMON.

(*** casting call, fun ***)
(* Definition ccallN {X Y} (fn: gname) (varg: X): itree Es Y := vret <- trigger (Call fn varg↑);; vret <- vret↓ǃ;; Ret vret. *)
(* Definition ccallU {X Y} (fn: gname) (varg: X): itree Es Y := vret <- trigger (Call fn varg↑);; vret <- vret↓?;; Ret vret. *)
(* Definition cfunN {X Y} (body: X -> itree Es Y): Any.t -> itree Es Any.t := *)
(*   fun varg => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑. *)
(* Definition cfunU {X Y} (body: X -> itree Es Y): Any.t -> itree Es Any.t := *)
(*   fun varg => varg <- varg↓?;; vret <- body varg;; Ret vret↑. *)

  (* Definition ccall {X Y} (fn: gname) (varg: X): itree Es Y := vret <- trigger (Call fn varg↑);; vret <- vret↓ǃ;; Ret vret. *)
  (* Definition cfun {X Y} (body: X -> itree Es Y): Any.t -> itree Es Any.t := *)
  (*   fun varg => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑. *)
  Context `{HasCallE: callE -< E}.
  Context `{HasEventE: eventE -< E}.

  Definition ccallN {X Y} (fn: gname) (varg: X): itree E Y := vret <- trigger (Call fn varg↑);; vret <- vret↓ǃ;; Ret vret.
  Definition ccallU {X Y} (fn: gname) (varg: X): itree E Y := vret <- trigger (Call fn varg↑);; vret <- vret↓?;; Ret vret.

  Definition cfunN {X Y} (body: X -> itree E Y): Any.t -> itree E Any.t :=
    fun '(varg) => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑.
  Definition cfunU {X Y} (body: X -> itree E Y): Any.t -> itree E Any.t :=
    fun '(varg) => varg <- varg↓?;; vret <- body varg;; Ret vret↑.

End EVENTSCOMMON.



Module Mod.
Section MOD.
  Context `{Sk.ld}.

  Record t: Type := mk {
    get_modsem: Sk.t -> ModSem.t;
    sk: Sk.t;
    enclose: ModSem.t := (get_modsem sk);
    (* get_modsem_Proper:> Proper ((≡) ==> eq) get_modsem; *)
    get_modsem_Proper:> forall sk0 sk1 (EQV: sk0 ≡ sk1) (WF: Sk.wf sk0), get_modsem sk0 = get_modsem sk1;
    get_modsem_extends:> forall sk0 sk1 (EQV: Sk.extends sk0 sk1) (WF: Sk.wf sk1), get_modsem sk1 ⊑ get_modsem sk0;
    get_modsem_extends_core:> forall sk0 sk1 (EQV: Sk.extends sk0 sk1) (WF: Sk.wf sk1), | get_modsem sk1 | ⊑ | get_modsem sk0 |;
  }
  .

  (* Definition wf (md: t): Prop := (<<SK: Sk.wf (md.(sk))>>). *)
  Definition wf (md: t): Prop := (<<WF: ModSem.wf md.(enclose)>> /\ <<SK: Sk.wf (md.(sk))>>).

  Program Definition core (md: t): t := mk (fun sk => |(md.(get_modsem) sk)| ) md.(sk) _ _ _.
  Next Obligation.
    erewrite get_modsem_Proper; et.
  Qed.
  Next Obligation.
    eapply get_modsem_extends_core; et.
  Qed.
  Next Obligation.
    rewrite ! ModSem.core_idemp.
    eapply get_modsem_extends_core; et.
  Qed.

  Global Program Instance bar: Bar t := core.

  Section BEH.

  Context {CONF: EMSConfig}.

  Definition compile (md: t): semantics :=
    ModSem.compile_itree (ModSem.initial_itr md.(enclose) (Some (wf md))).

  (* Record wf (md: t): Prop := mk_wf { *)
  (*   wf_sk: Sk.wf md.(sk); *)
  (* } *)
  (* . *)
  (*** wf about modsem is enforced in the semantics ***)

  Program Definition add (md0 md1: t): t := {|
    get_modsem := fun sk => (md0.(get_modsem) sk) ⊕ (md1.(get_modsem) sk);
    sk := md0.(sk) ⊕ md1.(sk);
  |}
  .
  Next Obligation.
    ii. rewrite ! (@get_modsem_Proper _ _ _ EQV); et.
  Qed.
  Next Obligation.
    admit "should hold".
  Qed.
  Next Obligation.
    admit "should hold".
  Qed.

  Global Program Instance add_OPlus: OPlus t := add.

  Program Definition empty: t := {|
    get_modsem := fun _ => ModSem.mk [] tt↑;
    sk := Sk.unit;
  |}
  .
  Next Obligation.
    ss.
  Qed.
  Next Obligation.
    ss.
  Qed.

  End BEH.

  Section REFINE.

  Definition cref' {CONF: EMSConfig} (md_tgt md_src: t): Prop :=
    forall (ctx: t), Beh.of_program (compile (ctx ⊕ md_tgt)) <1=
                       Beh.of_program (compile (ctx ⊕ md_src))
  .

  Definition cref (md_tgt md_src: t): Prop :=
    forall {CONF: EMSConfig}, cref' md_tgt md_src.

  Section CONF.
    Context {CONF: EMSConfig}.

    Global Program Instance cref_PreOrder: PreOrder cref.
    Next Obligation.
      ii. ss.
    Qed.
    Next Obligation.
      ii. eapply H0 in PR. eapply H1 in PR. eapply PR.
    Qed.

    Global Program Instance cref'_PreOrder: PreOrder cref'.
    Next Obligation. ii. ss. Qed.
    Next Obligation. ii. eapply H1. eapply H0. ss. Qed.
  End CONF.

  Definition bref {CONF: EMSConfig} (md_tgt md_src: t): Prop :=
    Beh.of_program (compile md_tgt) <1= Beh.of_program (compile md_src)
  .

  End REFINE.

End MOD.
End Mod.

Notation "(⊑B)" := Mod.bref (at level 50).
Notation "a ⊑B b" := (Mod.bref a b) (at level 50).



Global Existing Instance Sk.gdefs.
Arguments Sk.unit: simpl never.
Arguments Sk.add: simpl never.
Arguments Sk.wf: simpl never.







