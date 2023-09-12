Require Import Coqlib Algebra.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Any.
Require Import Skeleton.
Require Import Red IRed.
Require Export ModSemE.
Export Events.

Set Implicit Arguments.

(* Global Program Instance ReSum_trans (a b c: Type -> Type) *)
(*   `{ReSum _ IFun a b} `{ReSum _ IFun b c}: ReSum IFun a c | 200. *)
(* Next Obligation. *)
(*   ii. eauto. *)
(* Defined. *)

Lemma resum_itr_event
  Esub E F
  `{Esub -< E}
  `{E -< F}
  (R: Type)
  (i: Esub R)
  :
  (resum_itr (E:=E) (F:=F) (trigger i))
  =
    (trigger (subevent _ i) >>= (fun r => tau;; Ret r)).
Proof.
  Local Transparent resum_itr.
  unfold resum_itr in *.
  Local Opaque resum_itr.
  repeat rewrite interp_trigger. grind.
Qed.

Section FACTS.

  Ltac ired ::= repeat (try rewrite subst_bind;
                        try rewrite bind_bind; try rewrite bind_ret_l; try rewrite bind_ret_r; try rewrite bind_tau;
                        (* try rewrite interp_vis; *)
                        try rewrite interp_ret;
                        try rewrite interp_tau;
                        (* try rewrite interp_trigger *)
                        try rewrite interp_bind;

                        try rewrite interp_mrec_hit;
                        try rewrite interp_mrec_miss;
                        try rewrite interp_mrec_bind;
                        try rewrite interp_mrec_tau;
                        try rewrite interp_mrec_ret;

                        try rewrite interp_state_trigger;
                        try rewrite interp_state_bind;
                        try rewrite interp_state_tau;
                        try rewrite interp_state_ret;
                        try rewrite resum_itr_bind;
                        try rewrite resum_itr_ret;
                        try rewrite resum_itr_tau;
                        try rewrite resum_itr_event;
                        cbn
                  ).
  
  Lemma interp_Es_bind
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
        (prog: callE ~> itree Es)
        st0
    :
      interp_Es prog (v <- itr ;; ktr v) st0 =
      '(st1, v) <- interp_Es prog (itr) st0 ;; interp_Es prog (ktr v) st1
  .
  Proof. unfold interp_Es, interp_pE. grind. Qed.

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
      interp_Es p (trigger e) st0 =
        tau;; '(st1, r) <- (interp_Es p (p _ e) st0);; tau;; Ret (st1, r)
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
      tau;; tau;; tau;;
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
      interp_Es p (trigger e) st0 = r <- trigger e;; tau;; tau;; tau;; Ret (st0, r)
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

  Lemma interp_Es_unleftU
    prog L R st0 (r: L + R)
    :
    interp_Es prog (unleftU r) st0 = r <- unleftU r;; Ret (st0, r)
  .
  Proof.
    unfold unleftU. des_ifs.
    - rewrite interp_Es_ret. grind.
    - rewrite interp_Es_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma interp_Es_unleftN
    prog L R st0 (r: L + R)
    :
    interp_Es prog (unleftN r) st0 = r <- unleftN r;; Ret (st0, r)
  .
  Proof.
    unfold unleftN. des_ifs.
    - rewrite interp_Es_ret. grind.
    - rewrite interp_Es_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma interp_Es_unrightU
    prog L R st0 (r: L + R)
    :
    interp_Es prog (unrightU r) st0 = r <- unrightU r;; Ret (st0, r)
  .
  Proof.
    unfold unrightU. des_ifs.
    - rewrite interp_Es_triggerUB. unfold triggerUB. grind.
    - rewrite interp_Es_ret. grind.
  Qed.

  Lemma interp_Es_unrightN
    prog L R st0 (r: L + R)
    :
    interp_Es prog (unrightN r) st0 = r <- unrightN r;; Ret (st0, r)
  .
  Proof.
    unfold unrightN. des_ifs.
    - rewrite interp_Es_triggerNB. unfold triggerNB. grind.
    - rewrite interp_Es_ret. grind.
  Qed.

  Lemma interp_Es_assume
    prog st0 (P: Prop)
    :
    interp_Es prog (assume P) st0 = assume P;;; Ret (st0, tt)
  .
  Proof.
    unfold assume.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    des_ifs.
    - rewrite interp_Es_ret. grind.
    - unfold triggerUB. grind.
      repeat (try rewrite interp_Es_bind; try rewrite bind_bind).
      rewrite interp_Es_eventE. grind.
  Qed.

  Lemma interp_Es_guarantee
    prog st0 (P: Prop)
    :
    interp_Es prog (guarantee P) st0 = guarantee P;;; Ret (st0, tt)
  .
  Proof.
    unfold guarantee.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    des_ifs.
    - rewrite interp_Es_ret. grind.
    - unfold triggerNB. grind.
      repeat (try rewrite interp_Es_bind; try rewrite bind_bind).
      rewrite interp_Es_eventE. grind.
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

  Lemma focus_left_unleftU
        L R (r: L + R)
    :
      focus_left (unleftU r) = unleftU r
  .
  Proof.
    unfold unleftU. des_ifs.
    - rewrite focus_left_ret. grind.
    - rewrite focus_left_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma focus_left_unleftN
        L R (r: L + R)
    :
      focus_left (unleftN r) = unleftN r
  .
  Proof.
    unfold unleftN. des_ifs.
    - rewrite focus_left_ret. grind.
    - rewrite focus_left_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma focus_left_unrightU
        L R (r: L + R)
    :
      focus_left (unrightU r) = unrightU r
  .
  Proof.
    unfold unrightU. des_ifs.
    - rewrite focus_left_triggerUB. unfold triggerUB. grind.
    - rewrite focus_left_ret. grind.
  Qed.

  Lemma focus_left_unrightN
        L R (r: L + R)
    :
      focus_left (unrightN r) = unrightN r
  .
  Proof.
    unfold unrightN. des_ifs.
    - rewrite focus_left_triggerNB. unfold triggerNB. grind.
    - rewrite focus_left_ret. grind.
  Qed.

  Lemma focus_left_assume
        (P: Prop)
    :
      focus_left (assume P) = assume P;;; Ret (tt)
  .
  Proof.
    unfold assume.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    des_ifs.
    - rewrite focus_left_ret. grind.
    - unfold triggerUB. grind.
      rewrite focus_left_bind. rewrite focus_left_eventE. grind.
  Qed.

  Lemma focus_left_guarantee
        (P: Prop)
    :
      focus_left (guarantee P) = guarantee P;;; Ret (tt)
  .
  Proof.
    unfold guarantee.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    des_ifs.
    - rewrite focus_left_ret. grind.
    - unfold triggerNB. grind.
      rewrite focus_left_bind. rewrite focus_left_eventE. grind.
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

  Lemma focus_right_unleftU
        L R (r: L + R)
    :
      focus_right (unleftU r) = unleftU r
  .
  Proof.
    unfold unleftU. des_ifs.
    - rewrite focus_right_ret. grind.
    - rewrite focus_right_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma focus_right_unleftN
        L R (r: L + R)
    :
      focus_right (unleftN r) = unleftN r
  .
  Proof.
    unfold unleftN. des_ifs.
    - rewrite focus_right_ret. grind.
    - rewrite focus_right_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma focus_right_unrightU
        L R (r: L + R)
    :
      focus_right (unrightU r) = unrightU r
  .
  Proof.
    unfold unrightU. des_ifs.
    - rewrite focus_right_triggerUB. unfold triggerUB. grind.
    - rewrite focus_right_ret. grind.
  Qed.

  Lemma focus_right_unrightN
        L R (r: L + R)
    :
      focus_right (unrightN r) = unrightN r
  .
  Proof.
    unfold unrightN. des_ifs.
    - rewrite focus_right_triggerNB. unfold triggerNB. grind.
    - rewrite focus_right_ret. grind.
  Qed.

  Lemma focus_right_assume
        (P: Prop)
    :
      focus_right (assume P) = assume P;;; Ret (tt)
  .
  Proof.
    unfold assume.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    des_ifs.
    - rewrite focus_right_ret. grind.
    - unfold triggerUB. grind.
      rewrite focus_right_bind. rewrite focus_right_eventE. grind.
  Qed.

  Lemma focus_right_guarantee
        (P: Prop)
    :
      focus_right (guarantee P) = guarantee P;;; Ret (tt)
  .
  Proof.
    unfold guarantee, assume.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    des_ifs.
    - rewrite focus_right_ret. grind.
    - unfold triggerNB, triggerUB. grind.
      rewrite focus_right_bind. rewrite focus_right_eventE. grind.
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

  Lemma bar_unleftU
        L R (r: L + R)
    :
      bar (unleftU r) = unleftU r
  .
  Proof.
    unfold unleftU. des_ifs.
    - rewrite bar_ret. grind.
    - rewrite bar_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma bar_unleftN
        L R (r: L + R)
    :
      bar (unleftN r) = unleftN r
  .
  Proof.
    unfold unleftN. des_ifs.
    - rewrite bar_ret. grind.
    - rewrite bar_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma bar_unrightU
        L R (r: L + R)
    :
      bar (unrightU r) = unrightU r
  .
  Proof.
    unfold unrightU. des_ifs.
    - rewrite bar_triggerUB. unfold triggerUB. grind.
    - rewrite bar_ret. grind.
  Qed.

  Lemma bar_unrightN
        L R (r: L + R)
    :
      bar (unrightN r) = unrightN r
  .
  Proof.
    unfold unrightN. des_ifs.
    - rewrite bar_triggerNB. unfold triggerNB. grind.
    - rewrite bar_ret. grind.
  Qed.

  Lemma bar_assume
        (P: Prop)
    :
      bar (assume P) = assume P;;; Ret (tt)
  .
  Proof.
    unfold guarantee, assume.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    des_ifs.
    - rewrite bar_ret. grind.
    - unfold triggerNB, triggerUB. grind.
      rewrite bar_bind. rewrite bar_eventE. grind.
  Qed.

  Lemma bar_guarantee
        (P: Prop)
    :
      bar (guarantee P) = guarantee P;;; Ret (tt)
  .
  Proof.
    unfold guarantee, assume.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    des_ifs.
    - rewrite bar_ret. grind.
    - unfold triggerNB, triggerUB. grind.
      rewrite bar_bind. rewrite bar_eventE. grind.
  Qed.

  Lemma bar_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      bar itr0 = bar itr1
  .
  Proof. subst; refl. Qed.

End FACTS.
