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
  | SyscallOut (fn: gname) (args: Any.t) (rvs: Any.t -> Prop): eventE unit
  | SyscallIn (rv: Any.t): eventE unit
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

  Definition assume {E} `{eventE -< E} (P: Prop): itree E unit :=
    if excluded_middle_informative P then Ret tt else triggerUB.
    (* trigger (Take P) ;;; Ret tt. *)
  Definition guarantee {E} `{eventE -< E} (P: Prop): itree E unit :=
    if excluded_middle_informative P then Ret tt else triggerNB.
    (* trigger (Choose P) ;;; Ret tt. *)

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
  Definition pure_state {S E F} `{E -< F}: E ~> stateT S (itree F) := fun _ e s => x <- trigger e;; Ret (s, x).

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

  Definition Es: Type -> Type := ((callE +' pE) +' eventE).
  Definition Es': Type -> Type := (callE +' (pE +' eventE)).
  Definition prf: Es -< Es' := (ReSum_sum IFun sum1 (callE +' pE) eventE Es').

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

  Definition handle_pE `{eventE -< E}: pE ~> stateT p_state (itree (void1 +' E)) :=
    fun _ e p =>
      match e with
      | PPut p => Ret (p, tt)
      | PGet => Ret (p, p)
      end.
  Definition interp_pE `{eventE -< E}: itree (pE +' E) ~> stateT p_state (itree (void1 +' E)) :=
    (* State.interp_state (case_ ((fun _ e s0 => resum_itr (handle_pE e s0)): _ ~> stateT _ _) State.pure_state). *)
    State.interp_state (case_ handle_pE pure_state).

  (* Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (rst0: r_state) (pst0: p_state): itree eventE _ := *)
  (*   interp_pE (interp_rE (interp_mrec prog itr0) rst0) pst0 *)
  (* . *)
  Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: p_state): itree (void1 +' eventE) (p_state * _)%type :=
    let prog': callE ~> itree Es' := (fun _ ce => resum_itr (H:=prf) (prog _ ce)) in
    let itr0': itree Es' A := resum_itr (H:=prf) itr0 in
    '(st1, v) <- interp_pE (interp_mrec prog' itr0') st0;;
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
    fun itr => interp (case_ (case_ trivial_Handler core_h) trivial_Handler) itr
  .
  Global Program Instance ktree_Bar {R S}: Bar (ktree Es R S) := fun ktr x => |ktr x|.

  Definition focus_left: itree Es ~> itree Es :=
    fun _ itr =>
      interp (case_ (case_ trivial_Handler focus_left_h) trivial_Handler) itr
  .

  Definition focus_right: itree Es ~> itree Es :=
    fun _ itr =>
      interp (case_ (case_ trivial_Handler focus_right_h) trivial_Handler) itr
  .


  Global Program Instance bar_Proper {R}: Proper (A:=itree Es R -> itree Es R) ((≈) ==> (≈)) ( |-| ).
  Next Obligation.
    ii. unfold bar, itree_Bar. eapply eutt_interp; ss. ii. refl.
  Qed.

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
