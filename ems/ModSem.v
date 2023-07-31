Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export ModSemE.
Require Export AList.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Permutation.

Set Implicit Arguments.



Class EMSConfig := { finalize: Any.t -> option Any.t; initial_arg: Any.t }.

Module ModSemL.
Import EventsL.
Section MODSEML.


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
    fnsems: alist gname ((mname * Any.t) -> itree Es Any.t);
    initial_mrs: alist mname Any.t;
  }
  .

  Record wf (ms: t): Prop := mk_wf {
    wf_initial_mrs: NoDup (List.map fst ms.(initial_mrs));
  }
  .

  (*** using "Program Definition" makes the definition uncompilable; why?? ***)
  Definition add (ms0 ms1: t): t := {|
    (* sk := Sk.add md0.(sk) md1.(sk); *)
    (* initial_ld := URA.add (t:=URA.pointwise _ _) md0.(initial_ld) md1.(initial_ld); *)
    (* sem := fun _ '(Call fn args) => *)
    (*          (if List.in_dec string_dec fn md0.(sk) then md0.(sem) else md1.(sem)) _ (Call fn args); *)
    fnsems := app ms0.(fnsems) ms1.(fnsems);
    initial_mrs := app ms0.(initial_mrs) ms1.(initial_mrs);
  |}
  .



  Section INTERP.

  Variable ms: t.

  Definition prog: callE ~> itree Es :=
    fun _ '(Call mn fn args) =>
      n <- trigger (Take _);;
      assume(exists sem, nth_error ms.(fnsems) n = Some (fn, sem));;;
      '(_, sem) <- (nth_error ms.(fnsems) n)?;;
      rv <- (sem (mn, args));;
      Ret rv
  .



  Definition initial_p_state: p_state :=
    (fun mn => match alist_find mn ms.(initial_mrs) with
               | Some r => r
               | None => tt↑
               end).

  Context `{CONF: EMSConfig}.
  Definition initial_itr (P: option Prop): itree (eventE) Any.t :=
    match P with
    | None => Ret tt
    | Some P' => assume (<<WF: P'>>)
    end;;;
    snd <$> interp_Es prog (prog (Call mn_core "main" initial_arg)) (initial_p_state).



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
End MODSEML.
End ModSemL.
















(* Module Events. *)
Section EVENTS.

  Inductive callE: Type -> Type :=
  | Call (fn: gname) (args: Any.t): callE Any.t
  .

  Inductive pE: Type -> Type :=
  | PPut (p: Any.t): pE unit
  | PGet: pE Any.t
  .

  Definition Es: Type -> Type := (callE +' pE+' eventE).

  Definition handle_pE (mn: mname): pE ~> EventsL.pE :=
    fun _ pe =>
      match pe with
      | PPut a0 => (EventsL.PPut mn a0)
      | PGet => (EventsL.PGet mn)
      end
  .

  Definition handle_callE (mn: mname) `{EventsL.callE -< E}: callE ~> itree E :=
    fun _ '(Call fn args) =>
      r <- trigger (EventsL.Call mn fn args);;
      Ret r
  .

  Definition handle_all (mn: mname): Es ~> itree EventsL.Es.
    i. destruct X.
    { apply (handle_callE mn); assumption. }
    destruct s.
    { exact (trigger (handle_pE mn p)). }
    exact (trigger e).
  Defined.

  Definition transl_all (mn: mname): itree Es ~> itree EventsL.Es := interp (handle_all mn).






  Lemma transl_all_bind
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
        mn
    :
      transl_all mn (itr >>= ktr) = a <- (transl_all mn itr);; (transl_all mn (ktr a))
  .
  Proof. unfold transl_all. grind. Qed.

  Lemma transl_all_tau
        mn
        A
        (itr: itree Es A)
    :
      transl_all mn (tau;; itr) = tau;; (transl_all mn itr)
  .
  Proof. unfold transl_all. grind. Qed.

  Lemma transl_all_ret
        mn
        A
        (a: A)
    :
      transl_all mn (Ret a) = Ret a
  .
  Proof. unfold transl_all. grind. Qed.

  Lemma transl_all_callE
        mn
        fn args
    :
      transl_all mn (trigger (Call fn args)) =
      r <- (trigger (EventsL.Call mn fn args));;
      tau;; Ret r
  .
  Proof. unfold transl_all. rewrite unfold_interp. ss. grind. Qed.

  Lemma transl_all_pE
        mn
        T (e: pE T)
    :
      transl_all mn (trigger e) = r <- trigger (handle_pE mn e);; tau;; Ret r
  .
  Proof. dependent destruction e; ss; unfold transl_all; rewrite unfold_interp; ss; grind. Qed.

  Lemma transl_all_eventE
        mn
        T (e: eventE T)
    :
      transl_all mn (trigger e) = r <- trigger e;; tau;; Ret r
  .
  Proof. dependent destruction e; ss; unfold transl_all; rewrite unfold_interp; ss; grind. Qed.

  Lemma transl_all_triggerUB
        mn T
    :
      transl_all mn (triggerUB: itree _ T) = triggerUB
  .
  Proof. unfold triggerUB. unfold transl_all; rewrite unfold_interp; ss; grind. Qed.

  Lemma transl_all_triggerNB
        mn T
    :
      transl_all mn (triggerNB: itree _ T) = triggerNB
  .
  Proof. unfold triggerNB. unfold transl_all; rewrite unfold_interp; ss; grind. Qed.

End EVENTS.
(* End Events. *)

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

  Definition cfunN {X Y} (body: X -> itree E Y): (mname * Any.t) -> itree E Any.t :=
    fun '(_, varg) => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑.
  Definition cfunU {X Y} (body: X -> itree E Y): (mname * Any.t) -> itree E Any.t :=
    fun '(_, varg) => varg <- varg↓?;; vret <- body varg;; Ret vret↑.

End EVENTSCOMMON.



Module ModSem.
(* Import Events. *)
Section MODSEM.
  Record t: Type := mk {
    fnsems: list (gname * ((mname * Any.t) -> itree Es Any.t));
    mn: mname;
    initial_st: Any.t;
  }
  .

  Definition prog (ms: t): callE ~> itree Es :=
    fun _ '(Call fn args) =>
      n <- trigger (Take _);;
      assume(exists sem, nth_error ms.(fnsems) n = Some (fn, sem));;;
      '(_, sem) <- (nth_error ms.(fnsems) n)?;;
      '(mn, args) <- (Any.split args)ǃ;; mn <- mn↓ǃ;;
      (sem (mn, args))
  .

  (*** TODO: move to CoqlibC ***)
  (*** ss, cbn does not work as expected (in both version) ***)
  (* Definition map_fst A0 A1 B (f: A0 -> A1): (A0 * B) -> (A1 * B) := fun '(a, b) => (f a, b). *)
  (* Definition map_snd A B0 B1 (f: B0 -> B1): (A * B0) -> (A * B1) := fun '(a, b) => (a, f b). *)
  (* Definition map_fst A0 A1 B (f: A0 -> A1): (A0 * B) -> (A1 * B) := fun ab => match ab with (a, b) => (f a, b) end. *)
  (* Definition map_snd A B0 B1 (f: B0 -> B1): (A * B0) -> (A * B1) := fun ab => match ab with (a, b) => (a, f b) end. *)

  Definition lift (ms: t): ModSemL.t := {|
    ModSemL.fnsems := List.map (map_snd (fun sem args => transl_all ms.(mn) (sem args))) ms.(fnsems);
    ModSemL.initial_mrs := [(ms.(mn), ms.(initial_st))];
  |}
  .
  Coercion lift: t >-> ModSemL.t.

  Definition wf (ms: t): Prop := ModSemL.wf (lift ms).

  Context {CONF: EMSConfig}.
  Definition compile (ms: t) P: semantics := ModSemL.compile (lift ms) P.

End MODSEM.
End ModSem.

Coercion ModSem.lift: ModSem.t >-> ModSemL.t.




Module ModL.
Section MODL.
  Context `{Sk.ld}.

  Record t: Type := mk {
    get_modsem: Sk.t -> ModSemL.t;
    sk: Sk.t;
    enclose: ModSemL.t := (get_modsem (Sk.canon sk));
  }
  .

  Definition wf (md: t): Prop := (<<WF: ModSemL.wf md.(enclose)>> /\ <<SK: Sk.wf (md.(sk))>>).

  Section BEH.

  Context {CONF: EMSConfig}.

  Definition compile (md: t): semantics :=
    ModSemL.compile_itree (ModSemL.initial_itr md.(enclose) (Some (wf md))).

  (* Record wf (md: t): Prop := mk_wf { *)
  (*   wf_sk: Sk.wf md.(sk); *)
  (* } *)
  (* . *)
  (*** wf about modsem is enforced in the semantics ***)

  Definition add (md0 md1: t): t := {|
    get_modsem := fun sk =>
                    ModSemL.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
    sk := Sk.add md0.(sk) md1.(sk);
  |}
  .

  Definition empty: t := {|
    get_modsem := fun _ => ModSemL.mk [] [];
    sk := Sk.unit;
  |}
  .

  Lemma add_empty_r md: add md empty = md.
  Proof.
    destruct md; ss.
    unfold add, ModSemL.add. f_equal; ss.
    - extensionality skenv. destruct (get_modsem0 skenv); ss.
      repeat rewrite app_nil_r. auto.
    - eapply Sk.add_unit_r.
  Qed.

  Lemma add_empty_l md: add empty md = md.
  Proof.
    destruct md; ss.
    unfold add, ModSemL.add. f_equal; ss.
    { extensionality skenv. destruct (get_modsem0 skenv); ss. }
    { apply Sk.add_unit_l. }
  Qed.

  End BEH.

End MODL.
End ModL.



Module Mod.
Section MOD.
  Context `{Sk.ld}.

  Record t: Type := mk {
    get_modsem: Sk.t -> ModSem.t;
    sk: Sk.t;
  }
  .

  Definition lift (md: t): ModL.t := {|
    ModL.get_modsem := fun sk => md.(get_modsem) sk;
    ModL.sk := md.(sk);
  |}
  .

  Coercion lift: t >-> ModL.t.

  Definition wf (md: t): Prop := <<WF: ModL.wf (lift md)>>.

   Definition add_list (xs: list t): ModL.t :=
     fold_right ModL.add ModL.empty (List.map lift xs)
   .

   Lemma add_list_single: forall (x: t), add_list [x] = x.
   Proof. ii; cbn. rewrite ModL.add_empty_r. refl. Qed.

   Lemma add_list_cons
         x xs
     :
       (add_list (x :: xs)) = (ModL.add x (add_list xs))
   .
   Proof. ss. Qed.

   Lemma add_list_sk (mdl: list t)
     :
       ModL.sk (add_list mdl)
       =
       fold_right Sk.add Sk.unit (List.map sk mdl).
   Proof.
     induction mdl; ss. rewrite <- IHmdl. auto.
   Qed.

   Lemma add_list_initial_mrs (mdl: list t) (ske: Sk.t)
     :
       ModSemL.initial_mrs (ModL.get_modsem (add_list mdl) ske)
       =
       fold_right (@app _) [] (List.map (fun md => ModSemL.initial_mrs (get_modsem md ske)) mdl).
   Proof.
     induction mdl; ss. rewrite <- IHmdl. auto.
   Qed.

   Lemma add_list_fns (mdl: list t) (ske: Sk.t)
     :
       List.map fst (ModSemL.fnsems (ModL.get_modsem (add_list mdl) ske))
       =
       fold_right (@app _) [] (List.map (fun md => List.map fst (ModSemL.fnsems (get_modsem md ske))) mdl).
   Proof.
     induction mdl.
     { auto. }
     transitivity ((List.map fst (ModSemL.fnsems (get_modsem a ske)))++(fold_right (@app _) [] (List.map (fun md => List.map fst (ModSemL.fnsems (get_modsem md ske))) mdl))); auto.
     rewrite <- IHmdl. clear.
     ss. rewrite map_app. auto.
   Qed.

   Lemma add_list_fnsems (mdl: list t) (ske: Sk.t)
     :
       (ModSemL.fnsems (ModL.get_modsem (add_list mdl) ske))
       =
       fold_right (@app _) [] (List.map (fun md => (ModSemL.fnsems (get_modsem md ske))) mdl).
   Proof.
     induction mdl.
     { auto. }
     transitivity ((ModSemL.fnsems (get_modsem a ske))++(fold_right (@app _) [] (List.map (fun md => ModSemL.fnsems (get_modsem md ske)) mdl))); auto.
     rewrite <- IHmdl. clear. ss.
   Qed.
End MOD.
End Mod.

Coercion Mod.lift: Mod.t >-> ModL.t.













Module Equisatisfiability.
  Inductive pred: Type :=
  | true
  | false
  | meta (P: Prop)

  | disj: pred -> pred -> pred
  | conj: pred -> pred -> pred
  | neg: pred -> pred
  | impl: pred -> pred -> pred

  | univ (X: Type): (X -> pred) -> pred
  | exst (X: Type): (X -> pred) -> pred
  .

  (*** https://en.wikipedia.org/wiki/Negation_normal_form ***)
  Fixpoint embed (p: pred): itree eventE unit :=
    match p with
    | true => triggerUB
    | false => triggerNB
    | meta P => guarantee P

    | disj p0 p1 => b <- trigger (Choose _);; if (b: bool) then embed p0 else embed p1
    | conj p0 p1 => b <- trigger (Take _);; if (b: bool) then embed p0 else embed p1
    | neg p =>
      match p with
      | meta P => assume P
      | _ => triggerNB (*** we are assuming negation normal form ***)
      end
    | impl _ _ => triggerNB (*** we are assuming negation normal form ***)

    | @univ X k => x <- trigger (Take X);; embed (k x)
    | @exst X k => x <- trigger (Choose X);; embed (k x)
    end
  .

  (*** TODO: implication --> function call? ***)
  (***
P -> Q
~=
pname :=
  embed P

pqname :=
  (call pname) (finite times);;
  embed Q




(P -> Q) -> R
~=
pname :=
  embed P

pqname :=
  (call pname) (finite times);;
  embed Q

pqrname :=
  (call pqname) (finite times);;
  embed R
   ***)

  (* Fixpoint embed (p: pred) (is_pos: bool): itree eventE unit := *)
  (*   match p with *)
  (*   | true => triggerUB *)
  (*   | false => triggerNB *)
  (*   | meta P => guarantee P *)
  (*   | disj p0 p1 => b <- trigger (Choose _);; if (b: bool) then embed p0 is_pos else embed p1 is_pos *)
  (*   | conj p0 p1 => b <- trigger (Take _);; if (b: bool) then embed p0 is_pos else embed p1 is_pos *)
  (*   | @univ X k => x <- trigger (Take X);; embed (k x) is_pos *)
  (*   | @exst X k => x <- trigger (Choose X);; embed (k x) is_pos *)
  (*   | _ => triggerNB *)
  (*   end *)
  (* . *)
End Equisatisfiability.



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
    EventsL.interp_Es prog (unwrapU r) st0 = r <- unwrapU r;; Ret (st0, r)
.
Proof.
  unfold unwrapU. des_ifs.
  - rewrite EventsL.interp_Es_ret. grind.
  - rewrite EventsL.interp_Es_triggerUB. unfold triggerUB. grind.
Qed.

Lemma interp_Es_unwrapN
      prog R st0 (r: option R)
  :
    EventsL.interp_Es prog (unwrapN r) st0 = r <- unwrapN r;; Ret (st0, r)
.
Proof.
  unfold unwrapN. des_ifs.
  - rewrite EventsL.interp_Es_ret. grind.
  - rewrite EventsL.interp_Es_triggerNB. unfold triggerNB. grind.
Qed.

Lemma interp_Es_assume
      prog st0 (P: Prop)
  :
    EventsL.interp_Es prog (assume P) st0 = assume P;;; tau;; tau;; Ret (st0, tt)
.
Proof.
  unfold assume.
  repeat (try rewrite EventsL.interp_Es_bind; try rewrite bind_bind). grind.
  rewrite EventsL.interp_Es_eventE.
  repeat (try rewrite EventsL.interp_Es_bind; try rewrite bind_bind). grind.
  rewrite EventsL.interp_Es_ret.
  refl.
Qed.

Lemma interp_Es_guarantee
      prog st0 (P: Prop)
  :
    EventsL.interp_Es prog (guarantee P) st0 = guarantee P;;; tau;; tau;; Ret (st0, tt)
.
Proof.
  unfold guarantee.
  repeat (try rewrite EventsL.interp_Es_bind; try rewrite bind_bind). grind.
  rewrite EventsL.interp_Es_eventE.
  repeat (try rewrite EventsL.interp_Es_bind; try rewrite bind_bind). grind.
  rewrite EventsL.interp_Es_ret.
  refl.
Qed.





Require Import Red IRed.
Section AUX.
  Lemma interp_Es_ext
        prog R (itr0 itr1: itree _ R) st0
    :
      itr0 = itr1 -> EventsL.interp_Es prog itr0 st0 = EventsL.interp_Es prog itr1 st0
  .
  Proof. i; subst; refl. Qed.

  Global Program Instance interp_Es_rdb: red_database (mk_box (@EventsL.interp_Es)) :=
    mk_rdb
      1
      (mk_box EventsL.interp_Es_bind)
      (mk_box EventsL.interp_Es_tau)
      (mk_box EventsL.interp_Es_ret)
      (mk_box EventsL.interp_Es_pE)
      (mk_box EventsL.interp_Es_pE)
      (mk_box EventsL.interp_Es_callE)
      (mk_box EventsL.interp_Es_eventE)
      (mk_box EventsL.interp_Es_triggerUB)
      (mk_box EventsL.interp_Es_triggerNB)
      (mk_box interp_Es_unwrapU)
      (mk_box interp_Es_unwrapN)
      (mk_box interp_Es_assume)
      (mk_box interp_Es_guarantee)
      (mk_box interp_Es_ext)
  .

  Lemma transl_all_unwrapU
        mn R (r: option R)
    :
      transl_all mn (unwrapU r) = unwrapU r
  .
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite transl_all_ret. grind.
    - rewrite transl_all_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma transl_all_unwrapN
        mn R (r: option R)
    :
      transl_all mn (unwrapN r) = unwrapN r
  .
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite transl_all_ret. grind.
    - rewrite transl_all_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma transl_all_assume
        mn (P: Prop)
    :
      transl_all mn (assume P) = assume P;;; tau;; Ret (tt)
  .
  Proof.
    unfold assume.
    repeat (try rewrite transl_all_bind; try rewrite bind_bind). grind.
    rewrite transl_all_eventE.
    repeat (try rewrite transl_all_bind; try rewrite bind_bind). grind.
    rewrite transl_all_ret.
    refl.
  Qed.

  Lemma transl_all_guarantee
        mn (P: Prop)
    :
      transl_all mn (guarantee P) = guarantee P;;; tau;; Ret (tt)
  .
  Proof.
    unfold guarantee.
    repeat (try rewrite transl_all_bind; try rewrite bind_bind). grind.
    rewrite transl_all_eventE.
    repeat (try rewrite transl_all_bind; try rewrite bind_bind). grind.
    rewrite transl_all_ret.
    refl.
  Qed.

  Lemma transl_all_ext
        mn R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      transl_all mn itr0 = transl_all mn itr1
  .
  Proof. subst; refl. Qed.

  Global Program Instance transl_all_rdb: red_database (mk_box (@transl_all)) :=
    mk_rdb
      0
      (mk_box transl_all_bind)
      (mk_box transl_all_tau)
      (mk_box transl_all_ret)
      (mk_box transl_all_pE)
      (mk_box transl_all_pE)
      (mk_box transl_all_callE)
      (mk_box transl_all_eventE)
      (mk_box transl_all_triggerUB)
      (mk_box transl_all_triggerNB)
      (mk_box transl_all_unwrapU)
      (mk_box transl_all_unwrapN)
      (mk_box transl_all_assume)
      (mk_box transl_all_guarantee)
      (mk_box transl_all_ext)
  .
End AUX.
