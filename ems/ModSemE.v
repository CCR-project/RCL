Require Import Coqlib Algebra.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Any.
Require Import Skeleton.

Set Implicit Arguments.



Section EVENTSCOMMON.

  Variant eventE: Type -> Type :=
  | Choose (X: Type): eventE X
  | Take X: eventE X
  | Syscall (fn: gname) (args: Any.t) (rvs: Any.t -> Prop): eventE Any.t
  .

  (* Notation "'Choose' X" := (trigger (Choose X)) (at level 50, only parsing). *)
  (* Notation "'Take' X" := (trigger (Take X)) (at level 50, only parsing). *)

  Definition triggerUB {E A} `{eventE -< E}: itree E A :=
    v <- trigger (Take void);; match v: void with end
  .

  Definition triggerNB {E A} `{eventE -< E}: itree E A :=
    v <- trigger (Choose void);; match v: void with end
  .

  Definition unwrapN {E X} `{eventE -< E} (x: option X): itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerNB
    end.

  Definition unwrapU {E X} `{eventE -< E} (x: option X): itree E X :=
    match x with
    | Some x => Ret x
    | None => triggerUB
    end.

  Definition assume {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Take P) ;;; Ret tt.
  Definition guarantee {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Choose P) ;;; Ret tt.

  (* Notation "'unint?'" := (unwrapA <*> unint) (at level 57, only parsing). *)
  (* Notation "'unint﹗'" := (unwrapG <*> unint) (at level 57, only parsing). *)
  (* Notation "'Ret!' f" := (RetG f) (at level 57, only parsing). *)
  (* Notation "'Ret?' f" := (RetA f) (at level 57, only parsing). *)

  Definition unleftU {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerUB
    end.

  Definition unleftN {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
    match xy with
    | inl x => Ret x
    | inr y => triggerNB
    end.

  Definition unrightU {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
    match xy with
    | inl x => triggerUB
    | inr y => Ret y
    end.

  Definition unrightN {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
    match xy with
    | inl x => triggerNB
    | inr y => Ret y
    end.

End EVENTSCOMMON.

Notation "f '?'" := (unwrapU f) (at level 9, only parsing).
Notation "f 'ǃ'" := (unwrapN f) (at level 9, only parsing).
Notation "(?)" := (unwrapU) (only parsing).
Notation "(ǃ)" := (unwrapN) (only parsing).
Goal (tt ↑↓?) = Ret tt. rewrite Any.upcast_downcast. ss. Qed.
Goal (tt ↑↓ǃ) = Ret tt. rewrite Any.upcast_downcast. ss. Qed.







Section EVENTSCOMMON.

  Definition p_state: Type := (Any.t).

  (*** Same as State.pure_state, but does not use "Vis" directly ***)
  Definition pure_state {S E}: E ~> stateT S (itree E) := fun _ e s => x <- trigger e;; Ret (s, x).

  Lemma unfold_interp_state: forall {E F} {S R} (h: E ~> stateT S (itree F)) (t: itree E R) (s: S),
      interp_state h t s = _interp_state h (observe t) s.
  Proof. i. f. apply unfold_interp_state. Qed.

End EVENTSCOMMON.








Module Events.
Section EVENTS.

  Inductive callE: Type -> Type :=
  | Call (fn: gname) (args: Any.t): callE Any.t
  .

  Inductive pE: Type -> Type :=
  | PPut (p: Any.t): pE unit
  | PGet : pE Any.t
  .

  (*** TODO: we don't want to require "mname" here ***)
  (*** use dummy mname? ***)
  (* Definition FPut E `{rE -< E} (mn: mname) (fr: GRA): itree E unit := *)

  Definition Es: Type -> Type := (callE +' pE +' eventE).

  (* Inductive mdE: Type -> Type := *)
  (* | MPut (mn: mname) (r: GRA): mdE unit *)
  (* | MGet (mn: mname): mdE GRA *)
  (* . *)

  (* Inductive fnE: Type -> Type := *)
  (* | FPut (r: GRA): fnE unit *)
  (* | FGet: fnE GRA *)
  (* | FPush: fnE unit *)
  (* | FPop: fnE unit *)
  (* . *)






  (********************************************************************)
  (*************************** Interpretation *************************)
  (********************************************************************)

  Definition handle_pE `{eventE -< E}: pE ~> stateT p_state (itree E) :=
    fun _ e p =>
      match e with
      | PPut p => Ret (p, tt)
      | PGet => Ret (p, p)
      end.
  Definition interp_pE `{eventE -< E}: itree (pE +' E) ~> stateT p_state (itree E) :=
    (* State.interp_state (case_ ((fun _ e s0 => resum_itr (handle_pE e s0)): _ ~> stateT _ _) State.pure_state). *)
    State.interp_state (case_ handle_pE pure_state).

  (* Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (rst0: r_state) (pst0: p_state): itree eventE _ := *)
  (*   interp_pE (interp_rE (interp_mrec prog itr0) rst0) pst0 *)
  (* . *)
  Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: p_state): itree eventE (p_state * _)%type :=
    '(st1, v) <- interp_pE (interp_mrec prog itr0) st0;;
    Ret (st1, v)
  .
  
  Definition core_h: Handler pE Es := fun _ _ => triggerUB.
  (*   fun _ pE => match pE with *)
  (*               | PPut p => trigger (PPut p) *)
  (*               | PGet => triggerUB *)
  (*               end *)
  (* . *)

  Definition focus_left_h: Handler pE Es :=
    fun _ pE => match pE with
                | PPut l => (p <- trigger PGet;; '(_, r) <- (Any.split p)?;; trigger (PPut (Any.pair l r));;; Ret ())
                | PGet => (p <- trigger PGet;; '(l, _) <- (Any.split p)?;; Ret l)
                end
  .

  Definition focus_right_h: Handler pE Es :=
    fun _ pE => match pE with
                | PPut r => (p <- trigger PGet;; '(l, _) <- (Any.split p)?;; trigger (PPut (Any.pair l r));;; Ret ())
                | PGet => (p <- trigger PGet;; '(_, r) <- (Any.split p)?;; Ret r)
                end
  .

  Global Program Instance itree_Bar {R}: Bar (itree Es R) :=
    fun itr => interp (case_ trivial_Handler (case_ core_h trivial_Handler)) itr
  .
  Global Program Instance ktree_Bar {R S}: Bar (ktree Es R S) := fun ktr x => |ktr x|.

  Definition focus_left: itree Es ~> itree Es :=
    fun _ itr =>
      interp (case_ trivial_Handler (case_ focus_left_h trivial_Handler)) itr
  .

  Definition focus_right: itree Es ~> itree Es :=
    fun _ itr =>
      interp (case_ trivial_Handler (case_ focus_right_h trivial_Handler)) itr
  .


  Global Program Instance bar_Proper {R}: Proper (A:=itree Es R -> itree Es R) ((≈) ==> (≈)) ( |-| ).
  Next Obligation.
    ii. unfold bar, itree_Bar. eapply eutt_interp; ss. ii. refl.
  Qed.



  Lemma interp_Es_bind
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
        (prog: callE ~> itree Es)
        st0
    :
      interp_Es prog (v <- itr ;; ktr v) st0 =
      '(st1, v) <- interp_Es prog (itr) st0 ;; interp_Es prog (ktr v) st1
  .
  Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_tau
        (prog: callE ~> itree Es)
        A
        (itr: itree Es A)
        st0
    :
      interp_Es prog (tau;; itr) st0 = tau;; interp_Es prog itr st0
  .
  Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_ret
        T
        prog st0 (v: T)
    :
      interp_Es prog (Ret v) st0 = Ret (st0, v)
  .
  Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_callE
        p st0 T
        (* (e: Es Σ) *)
        (e: callE T)
    :
      interp_Es p (trigger e) st0 = tau;; (interp_Es p (p _ e) st0)
  .
  Proof. unfold interp_Es, interp_pE. des_ifs. grind. Qed.

  Lemma interp_Es_pE
        p st0
        (* (e: Es Σ) *)
        T
        (e: pE T)
    :
      interp_Es p (trigger e) st0 =
      '(st1, r) <- handle_pE e st0;;
      tau;; tau;;
      Ret (st1, r)
  .
  Proof.
    unfold interp_Es, interp_pE. grind.
  Qed.

  Lemma interp_Es_eventE
        p st0
        (* (e: Es Σ) *)
        T
        (e: eventE T)
    :
      interp_Es p (trigger e) st0 = r <- trigger e;; tau;; tau;; Ret (st0, r)
  .
  Proof.
    unfold interp_Es, interp_pE. grind.
    unfold pure_state. grind.
  Qed.

  Lemma interp_Es_triggerUB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (interp_Es prog (triggerUB) st0: itree eventE (_ * A)) = triggerUB
  .
  Proof.
    unfold interp_Es, interp_pE, pure_state, triggerUB. grind.
  Qed.

  Lemma interp_Es_triggerNB
        (prog: callE ~> itree Es)
        st0
        A
    :
      (interp_Es prog (triggerNB) st0: itree eventE (_ * A)) = triggerNB
  .
  Proof.
    unfold interp_Es, interp_pE, pure_state, triggerNB. grind.
  Qed.
  
  Lemma interp_Es_unwrapU
    prog R st0 (r: option R)
    :
    interp_Es prog (unwrapU r) st0 = r <- unwrapU r;; Ret (st0, r)
  .
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite interp_Es_ret. grind.
    - rewrite interp_Es_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma interp_Es_unwrapN
    prog R st0 (r: option R)
    :
    interp_Es prog (unwrapN r) st0 = r <- unwrapN r;; Ret (st0, r)
  .
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite interp_Es_ret. grind.
    - rewrite interp_Es_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma interp_Es_assume
    prog st0 (P: Prop)
    :
    interp_Es prog (assume P) st0 = assume P;;; tau;; tau;; Ret (st0, tt)
  .
  Proof.
    unfold assume.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    rewrite interp_Es_eventE.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    rewrite interp_Es_ret.
    refl.
  Qed.

  Lemma interp_Es_guarantee
    prog st0 (P: Prop)
    :
    interp_Es prog (guarantee P) st0 = guarantee P;;; tau;; tau;; Ret (st0, tt)
  .
  Proof.
    unfold guarantee.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    rewrite interp_Es_eventE.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    rewrite interp_Es_ret.
    refl.
  Qed.

  Lemma interp_Es_ext
        prog R (itr0 itr1: itree _ R) st0
    :
      itr0 = itr1 -> interp_Es prog itr0 st0 = interp_Es prog itr1 st0
  .
  Proof. i; subst; refl. Qed.
  Opaque interp_Es.




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
      r <- (trigger (Call fn args));;
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
      r <- (trigger (Call fn args));;
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




  Lemma bar_bind
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
    :
      bar (itr >>= ktr) = a <- (bar itr);; (bar (ktr a))
  .
  Proof. unfold bar, itree_Bar. grind. Qed.

  Lemma bar_tau
        A
        (itr: itree Es A)
    :
      bar (tau;; itr) = tau;; (bar itr)
  .
  Proof. unfold bar, itree_Bar. grind. Qed.

  Lemma bar_ret
        A
        (a: A)
    :
      bar (Ret a) = Ret a
  .
  Proof. unfold bar, itree_Bar. grind. Qed.

  Lemma bar_callE
        fn args
    :
      bar (trigger (Call fn args)) =
      r <- (trigger (Call fn args));;
      tau;; Ret r
  .
  Proof. unfold bar, itree_Bar. rewrite unfold_interp. ss. grind. Qed.

  Lemma bar_pE
        T (e: pE T)
    :
      bar (trigger e) = r <- (core_h e);; tau;; Ret r
  .
  Proof. dependent destruction e; ss; unfold bar, itree_Bar; rewrite unfold_interp; ss; grind. Qed.

  Lemma bar_eventE
        T (e: eventE T)
    :
      bar (trigger e) = r <- trigger e;; tau;; Ret r
  .
  Proof. dependent destruction e; ss; unfold bar, itree_Bar; rewrite unfold_interp; ss; grind. Qed.

  Lemma bar_triggerUB
        T
    :
      bar (triggerUB: itree _ T) = triggerUB
  .
  Proof. unfold triggerUB. unfold bar, itree_Bar; rewrite unfold_interp; ss; grind. Qed.

  Lemma bar_triggerNB
        T
    :
      bar (triggerNB: itree _ T) = triggerNB
  .
  Proof. unfold triggerNB. unfold bar, itree_Bar; rewrite unfold_interp; ss; grind. Qed.


  Lemma bar_unwrapU
        R (r: option R)
    :
      bar (unwrapU r) = unwrapU r
  .
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite bar_ret. grind.
    - rewrite bar_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma bar_unwrapN
        R (r: option R)
    :
      bar (unwrapN r) = unwrapN r
  .
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite bar_ret. grind.
    - rewrite bar_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma bar_assume
        (P: Prop)
    :
      bar (assume P) = assume P;;; tau;; Ret (tt)
  .
  Proof.
    unfold assume.
    repeat (try rewrite bar_bind; try rewrite bind_bind). grind.
    rewrite bar_eventE.
    repeat (try rewrite bar_bind; try rewrite bind_bind). grind.
    rewrite bar_ret.
    refl.
  Qed.

  Lemma bar_guarantee
        (P: Prop)
    :
      bar (guarantee P) = guarantee P;;; tau;; Ret (tt)
  .
  Proof.
    unfold guarantee.
    repeat (try rewrite bar_bind; try rewrite bind_bind). grind.
    rewrite bar_eventE.
    repeat (try rewrite bar_bind; try rewrite bind_bind). grind.
    rewrite bar_ret.
    refl.
  Qed.

  Lemma bar_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      bar itr0 = bar itr1
  .
  Proof. subst; refl. Qed.


End EVENTS.
End Events.
Opaque Events.interp_Es.


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
  Context `{HasCallE: Events.callE -< E}.
  Context `{HasEventE: eventE -< E}.

  Definition ccallN {X Y} (fn: gname) (varg: X): itree E Y := vret <- trigger (Events.Call fn varg↑);; vret <- vret↓ǃ;; Ret vret.
  Definition ccallU {X Y} (fn: gname) (varg: X): itree E Y := vret <- trigger (Events.Call fn varg↑);; vret <- vret↓?;; Ret vret.

  Definition cfunN {X Y} (body: X -> itree E Y): Any.t -> itree E Any.t :=
    fun '(varg) => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑.
  Definition cfunU {X Y} (body: X -> itree E Y): Any.t -> itree E Any.t :=
    fun '(varg) => varg <- varg↓?;; vret <- body varg;; Ret vret↑.

End EVENTSCOMMON.
