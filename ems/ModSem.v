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

  Global Program Instance equiv: Equiv t :=
    fun ms0 ms1 => <<ST: ms0.(initial_st) = ms1.(initial_st)>> /\ <<SEM: Permutation ms0.(fnsems) ms1.(fnsems)>>
  .

  Global Program Instance equiv_Equivalence: Equivalence ((≡)).
  Next Obligation.
    ii. rr. esplits; et.
  Qed.
  Next Obligation.
    ii. rr. rr in H. des. esplits; et. sym; et.
  Qed.
  Next Obligation.
    ii. rr. rr in H. rr in H0. des. esplits; ss; etrans; et.
  Qed.

  Record wf (ms: t): Prop := mk_wf {
    wf_fnsems: NoDup (List.map fst ms.(fnsems));
  }
  .

  Global Program Instance wf_Proper: Proper ((≡) ==> impl) wf.
  Next Obligation.
    ii; ss.
    rr in H. inv H0. econs; et. des; subst. eapply Permutation_NoDup; revgoals; et. eapply Permutation_map; et.
  Qed.



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

  Global Program Instance add_Proper: Proper ((≡) ==> (≡) ==> (≡)) ((⊕)).
  Next Obligation.
    ii. rr in H. rr in H0. des. rr. esplits; et.
    - ss. f_equal; et.
    - ss. rewrite Permutation_app; et.
      + rewrite Permutation_map; et.
      + rewrite Permutation_map; et.
  Qed.


  Section INTERP.

  Variable ms: t.

  Definition prog: callE ~> itree Es :=
    fun _ '(Call fn args) =>
      sem <- (alist_find fn ms.(fnsems))?;;
      rv <- (sem args);;
      Ret rv
  .

  (* Definition prog: callE ~> itree Es := *)
  (*   fun _ '(Call fn args) => *)
  (*     n <- trigger (Take _);; *)
  (*     assume(exists sem, nth_error ms.(fnsems) n = Some (fn, sem));;; *)
  (*     '(_, sem) <- (nth_error ms.(fnsems) n)?;; *)
  (*     rv <- (sem args);; *)
  (*     Ret rv *)
  (* . *)



  Definition initial_p_state: p_state := ms.(initial_st).

  Context `{CONF: EMSConfig}.
  Definition initial_itr (P: option Prop): itree (eventE) Any.t :=
    match P with
    | None => Ret tt
    | Some P' => assume (<<WF: P'>>)
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

  Lemma initial_itr_not_wf P
        (WF: ~ P)
        tr
    :
      Beh.of_program (compile_itree (initial_itr (Some P))) tr.
  Proof.
    eapply Beh.ub_top. pfold. econsr; ss; et. rr. ii; ss.
    unfold initial_itr, assume in *. rewrite bind_bind in STEP.
    eapply step_trigger_take_iff in STEP. des. subst. ss.
  Qed.

  Lemma compile_not_wf P
        (WF: ~ P)
        tr
    :
      Beh.of_program (compile (Some P)) tr.
  Proof.
    eapply initial_itr_not_wf; et.
  Qed.

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

  End INTERP.
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
    get_modsem_Proper:> Proper ((≡) ==> eq) get_modsem;
  }
  .

  (* Definition wf (md: t): Prop := (<<SK: Sk.wf (md.(sk))>>). *)
  Definition wf (md: t): Prop := (<<WF: ModSem.wf md.(enclose)>> /\ <<SK: Sk.wf (md.(sk))>>).

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
    ii. rewrite ! (@get_modsem_Proper _ _ _ H0); et.
  Qed.

  Global Program Instance add_OPlus: OPlus t := add.

  Program Definition empty: t := {|
    get_modsem := fun _ => ModSem.mk [] tt↑;
    sk := Sk.unit;
  |}
  .
  Next Obligation.
    ii. f_equiv.
  Qed.

  End BEH.

End MOD.
End Mod.



Global Existing Instance Sk.gdefs.
Arguments Sk.unit: simpl never.
Arguments Sk.add: simpl never.
Arguments Sk.wf: simpl never.
Coercion Sk.load_skenv: Sk.t >-> SkEnv.t.
Global Opaque Sk.load_skenv.


(*** TODO: Move to ModSem.v ***)
Lemma interp_Es_unwrapU
      prog R st0 (r: option R)
  :
    Events.interp_Es prog (unwrapU r) st0 = r <- unwrapU r;; Ret (st0, r)
.
Proof.
  unfold unwrapU. des_ifs.
  - rewrite Events.interp_Es_ret. grind.
  - rewrite Events.interp_Es_triggerUB. unfold triggerUB. grind.
Qed.

Lemma interp_Es_unwrapN
      prog R st0 (r: option R)
  :
    Events.interp_Es prog (unwrapN r) st0 = r <- unwrapN r;; Ret (st0, r)
.
Proof.
  unfold unwrapN. des_ifs.
  - rewrite Events.interp_Es_ret. grind.
  - rewrite Events.interp_Es_triggerNB. unfold triggerNB. grind.
Qed.

Lemma interp_Es_assume
      prog st0 (P: Prop)
  :
    Events.interp_Es prog (assume P) st0 = assume P;;; tau;; tau;; Ret (st0, tt)
.
Proof.
  unfold assume.
  repeat (try rewrite Events.interp_Es_bind; try rewrite bind_bind). grind.
  rewrite Events.interp_Es_eventE.
  repeat (try rewrite Events.interp_Es_bind; try rewrite bind_bind). grind.
  rewrite Events.interp_Es_ret.
  refl.
Qed.

Lemma interp_Es_guarantee
      prog st0 (P: Prop)
  :
    Events.interp_Es prog (guarantee P) st0 = guarantee P;;; tau;; tau;; Ret (st0, tt)
.
Proof.
  unfold guarantee.
  repeat (try rewrite Events.interp_Es_bind; try rewrite bind_bind). grind.
  rewrite Events.interp_Es_eventE.
  repeat (try rewrite Events.interp_Es_bind; try rewrite bind_bind). grind.
  rewrite Events.interp_Es_ret.
  refl.
Qed.





Require Import Red IRed.
Section AUX.
  Lemma interp_Es_ext
        prog R (itr0 itr1: itree _ R) st0
    :
      itr0 = itr1 -> Events.interp_Es prog itr0 st0 = Events.interp_Es prog itr1 st0
  .
  Proof. i; subst; refl. Qed.

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

  Lemma focus_left_bind
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
    :
      focus_left (itr >>= ktr) = a <- (focus_left itr);; (focus_left (ktr a))
  .
  Proof. unfold focus_left. grind. Qed.

  Lemma focus_left_tau
        A
        (itr: itree Es A)
    :
      focus_left (tau;; itr) = tau;; (focus_left itr)
  .
  Proof. unfold focus_left. grind. Qed.

  Lemma focus_left_ret
        A
        (a: A)
    :
      focus_left (Ret a) = Ret a
  .
  Proof. unfold focus_left. grind. Qed.

  Lemma focus_left_callE
        fn args
    :
      focus_left (trigger (Call fn args)) =
      r <- (trigger (Events.Call fn args));;
      tau;; Ret r
  .
  Proof. unfold focus_left. rewrite unfold_interp. ss. grind. Qed.

  Lemma focus_left_pE
        T (e: pE T)
    :
      focus_left (trigger e) = r <- (focus_left_h e);; tau;; Ret r
  .
  Proof. dependent destruction e; ss; unfold focus_left; rewrite unfold_interp; ss; grind. Qed.

  Lemma focus_left_eventE
        T (e: eventE T)
    :
      focus_left (trigger e) = r <- trigger e;; tau;; Ret r
  .
  Proof. dependent destruction e; ss; unfold focus_left; rewrite unfold_interp; ss; grind. Qed.

  Lemma focus_left_triggerUB
        T
    :
      focus_left (triggerUB: itree _ T) = triggerUB
  .
  Proof. unfold triggerUB. unfold focus_left; rewrite unfold_interp; ss; grind. Qed.

  Lemma focus_left_triggerNB
        T
    :
      focus_left (triggerNB: itree _ T) = triggerNB
  .
  Proof. unfold triggerNB. unfold focus_left; rewrite unfold_interp; ss; grind. Qed.


  Lemma focus_left_unwrapU
        R (r: option R)
    :
      focus_left (unwrapU r) = unwrapU r
  .
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite focus_left_ret. grind.
    - rewrite focus_left_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma focus_left_unwrapN
        R (r: option R)
    :
      focus_left (unwrapN r) = unwrapN r
  .
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite focus_left_ret. grind.
    - rewrite focus_left_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma focus_left_assume
        (P: Prop)
    :
      focus_left (assume P) = assume P;;; tau;; Ret (tt)
  .
  Proof.
    unfold assume.
    repeat (try rewrite focus_left_bind; try rewrite bind_bind). grind.
    rewrite focus_left_eventE.
    repeat (try rewrite focus_left_bind; try rewrite bind_bind). grind.
    rewrite focus_left_ret.
    refl.
  Qed.

  Lemma focus_left_guarantee
        (P: Prop)
    :
      focus_left (guarantee P) = guarantee P;;; tau;; Ret (tt)
  .
  Proof.
    unfold guarantee.
    repeat (try rewrite focus_left_bind; try rewrite bind_bind). grind.
    rewrite focus_left_eventE.
    repeat (try rewrite focus_left_bind; try rewrite bind_bind). grind.
    rewrite focus_left_ret.
    refl.
  Qed.

  Lemma focus_left_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      focus_left itr0 = focus_left itr1
  .
  Proof. subst; refl. Qed.

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

  Lemma focus_right_bind
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
    :
      focus_right (itr >>= ktr) = a <- (focus_right itr);; (focus_right (ktr a))
  .
  Proof. unfold focus_right. grind. Qed.

  Lemma focus_right_tau
        A
        (itr: itree Es A)
    :
      focus_right (tau;; itr) = tau;; (focus_right itr)
  .
  Proof. unfold focus_right. grind. Qed.

  Lemma focus_right_ret
        A
        (a: A)
    :
      focus_right (Ret a) = Ret a
  .
  Proof. unfold focus_right. grind. Qed.

  Lemma focus_right_callE
        fn args
    :
      focus_right (trigger (Call fn args)) =
      r <- (trigger (Events.Call fn args));;
      tau;; Ret r
  .
  Proof. unfold focus_right. rewrite unfold_interp. ss. grind. Qed.

  Lemma focus_right_pE
        T (e: pE T)
    :
      focus_right (trigger e) = r <- (focus_right_h e);; tau;; Ret r
  .
  Proof. dependent destruction e; ss; unfold focus_right; rewrite unfold_interp; ss; grind. Qed.

  Lemma focus_right_eventE
        T (e: eventE T)
    :
      focus_right (trigger e) = r <- trigger e;; tau;; Ret r
  .
  Proof. dependent destruction e; ss; unfold focus_right; rewrite unfold_interp; ss; grind. Qed.

  Lemma focus_right_triggerUB
        T
    :
      focus_right (triggerUB: itree _ T) = triggerUB
  .
  Proof. unfold triggerUB. unfold focus_right; rewrite unfold_interp; ss; grind. Qed.

  Lemma focus_right_triggerNB
        T
    :
      focus_right (triggerNB: itree _ T) = triggerNB
  .
  Proof. unfold triggerNB. unfold focus_right; rewrite unfold_interp; ss; grind. Qed.


  Lemma focus_right_unwrapU
        R (r: option R)
    :
      focus_right (unwrapU r) = unwrapU r
  .
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite focus_right_ret. grind.
    - rewrite focus_right_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma focus_right_unwrapN
        R (r: option R)
    :
      focus_right (unwrapN r) = unwrapN r
  .
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite focus_right_ret. grind.
    - rewrite focus_right_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma focus_right_assume
        (P: Prop)
    :
      focus_right (assume P) = assume P;;; tau;; Ret (tt)
  .
  Proof.
    unfold assume.
    repeat (try rewrite focus_right_bind; try rewrite bind_bind). grind.
    rewrite focus_right_eventE.
    repeat (try rewrite focus_right_bind; try rewrite bind_bind). grind.
    rewrite focus_right_ret.
    refl.
  Qed.

  Lemma focus_right_guarantee
        (P: Prop)
    :
      focus_right (guarantee P) = guarantee P;;; tau;; Ret (tt)
  .
  Proof.
    unfold guarantee.
    repeat (try rewrite focus_right_bind; try rewrite bind_bind). grind.
    rewrite focus_right_eventE.
    repeat (try rewrite focus_right_bind; try rewrite bind_bind). grind.
    rewrite focus_right_ret.
    refl.
  Qed.

  Lemma focus_right_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      focus_right itr0 = focus_right itr1
  .
  Proof. subst; refl. Qed.

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
End AUX.






Section REFINE.
  Context `{Sk.ld}.

  Definition cref' {CONF: EMSConfig} (md_tgt md_src: Mod.t): Prop :=
    forall (ctx: Mod.t), Beh.of_program (Mod.compile (ctx ⊕ md_tgt)) <1=
                           Beh.of_program (Mod.compile (ctx ⊕ md_src))
  .

  Definition cref (md_tgt md_src: Mod.t): Prop :=
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

  Definition bref {CONF: EMSConfig} (md_tgt md_src: Mod.t): Prop :=
    Beh.of_program (Mod.compile md_tgt) <1= Beh.of_program (Mod.compile md_src)
  .

End REFINE.

Notation "(⊑)" := cref (at level 50).
Notation "a ⊑ b" := (cref a b) (at level 50).
Notation "(⊑B)" := bref (at level 50).
Notation "a ⊑B b" := (bref a b) (at level 50).
