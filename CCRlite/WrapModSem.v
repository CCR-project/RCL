Require Import Coqlib ModSemFacts ModSem Algebra Any AList.
From stdpp Require Import base gmap.

Set Implicit Arguments.

Record cond: Type := mk_cond {
    precond: Any.t -> Prop;
    postcond: Any.t -> Any.t -> Prop;
}.

Global Instance cond_eps: Eps cond := mk_cond top1 top2.

Global Instance cond_ops: OPlus cond :=
  fun c0 c1 =>
    mk_cond
      (c0.(precond) /1\ c1.(precond))
      (c0.(postcond) /2\ c1.(postcond))
.

Global Instance cond_equiv: Equiv cond := eq.

Global Program Instance cond_OPlusFacts: OPlusFacts (T:=cond).
Next Obligation.
  i. rr. destruct a, b; ss.
  compute. f_equal.
  - extensionalities x. eapply prop_ext. tauto.
  - extensionalities x y. eapply prop_ext. tauto.
Qed.
Next Obligation.
  i. rr. destruct a, b; ss.
  compute. f_equal.
  - extensionalities x. eapply prop_ext. tauto.
  - extensionalities x y. eapply prop_ext. tauto.
Qed.

Global Program Instance cond_EpsFacts: EpsFacts (T:=cond).
Next Obligation.
  ii. destruct a; ss.
  compute. f_equal.
  - extensionalities x. eapply prop_ext. tauto.
  - extensionalities x y. eapply prop_ext. tauto.
Qed.
Next Obligation.
  ii. destruct a; ss.
  compute. f_equal.
  - extensionalities x. eapply prop_ext. tauto.
  - extensionalities x y. eapply prop_ext. tauto.
Qed.

(* Variant triopt (T: Type): Type := *)
(* | empty *)
(* | err *)
(* | just (t: T) *)
(* . *)

(* Definition conds: Type := string -> pointed (option cond). *)
Definition conds: Type := string -> cond.

Global Instance conds_eps: Eps conds := fun _ => ε.

Global Instance conds_oplus: OPlus conds :=
  fun c0 c1 fn => (c0 fn) ⊕ (c1 fn).

Global Instance conds_equiv: Equiv conds := eq.

Global Program Instance conds_OPlusFacts: OPlusFacts (T:=conds).
Next Obligation.
  ii. unfold oplus, conds_oplus.
  rr. extensionalities x. rewrite oplus_comm. ss.
Qed.
Next Obligation.
  ii. unfold oplus, conds_oplus.
  rr. extensionalities x. rewrite oplus_assoc. ss.
Qed.



Section WRAP.

  Definition wrap_h (cs: conds): Handler callE Es :=
    fun _ ce =>
      match ce with
      | Call fn arg =>
          let c := (cs fn) in
          guarantee(c.(precond) arg);;;
          ret <- trigger (Call fn arg);;
          assume(c.(postcond) arg ret);;;
          Ret ret
      end
  .

  Global Instance wrap_itree {R}: Wrap conds (itree Es R) :=
    fun cs itr => interp (case_ (bif:=sum1) (wrap_h cs) trivial_Handler) itr
  .

  Global Instance wrap_ktree: Wrap conds (string * (Any.t -> itree Es Any.t)) :=
    fun cs nf =>
      (nf.1, fun arg =>
               let c := (cs nf.1) in
               assume(c.(precond) arg);;;
               ret <- 𝑤_{cs} (nf.2 arg);;
               guarantee(c.(postcond) arg ret);;;
               Ret ret
      )
  .

  Global Instance wrap_fnsems: Wrap conds (alist string (Any.t -> itree Es Any.t)) :=
    fun cs nfs => List.map (fun nf => 𝑤_{cs} nf) nfs
  .

  Global Instance wrap_modsem_: Wrap conds (ModSem._t) :=
    fun cs ms => ModSem.mk (𝑤_{cs} ms.(ModSem.fnsems)) ms.(ModSem.initial_st)
  .
      
  Global Instance wrap_modsem: Wrap conds (ModSem.t) :=
    fun cs ms =>
      match ms with
      | just ms => 𝑤_{cs} ms
      | mytt => mytt
      end
  .

End WRAP.

Require Import Red IRed.

Section WRAPFACTS.
  Variable cs: conds.
  Lemma wrap_bind
        A B
        (itr: itree Es A) (ktr: A -> itree Es B)
    :
      𝑤_{cs} (itr >>= ktr) = a <- (𝑤_{cs} itr);; (𝑤_{cs} (ktr a))
  .
  Proof. unfold wrap, wrap_itree. grind. Qed.

  Lemma wrap_tau
        A
        (itr: itree Es A)
    :
      𝑤_{cs} (tau;; itr) = tau;; (𝑤_{cs} itr)
  .
  Proof. unfold wrap, wrap_itree. grind. Qed.

  Lemma wrap_ret
        A
        (a: A)
    :
      𝑤_{cs} (Ret a) = Ret a
  .
  Proof. unfold wrap, wrap_itree. grind. Qed.

  Lemma wrap_callE
        R (ce: callE R)
    :
      𝑤_{cs} (trigger ce) = r <- wrap_h cs ce;; tau;; Ret r
  .
  Proof. unfold wrap, wrap_itree. rewrite unfold_interp. ss. grind. Qed.

  Lemma wrap_pE
        T (e: pE T)
    :
      𝑤_{cs} (trigger e) = r <- (trigger e);; tau;; Ret r
  .
  Proof. dependent destruction e; ss; unfold wrap, wrap_itree;
           rewrite unfold_interp; ss; grind. Qed.

  Lemma wrap_eventE
        T (e: eventE T)
    :
      𝑤_{cs} (trigger e) = r <- trigger e;; tau;; Ret r
  .
  Proof. dependent destruction e; ss; unfold wrap, wrap_itree;
           rewrite unfold_interp; ss; grind. Qed.

  Lemma wrap_triggerUB
        T
    :
      𝑤_{cs} (triggerUB: itree _ T) = triggerUB
  .
  Proof. unfold triggerUB. unfold wrap, wrap_itree; rewrite unfold_interp; ss; grind. Qed.

  Lemma wrap_triggerNB
        T
    :
      𝑤_{cs} (triggerNB: itree _ T) = triggerNB
  .
  Proof. unfold triggerNB. unfold wrap, wrap_itree; rewrite unfold_interp; ss; grind. Qed.


  Lemma wrap_unwrapU
        R (r: option R)
    :
      𝑤_{cs} (unwrapU r) = unwrapU r
  .
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite wrap_ret. grind.
    - rewrite wrap_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma wrap_unwrapN
        R (r: option R)
    :
      𝑤_{cs} (unwrapN r) = unwrapN r
  .
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite wrap_ret. grind.
    - rewrite wrap_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma wrap_unleftU
        L R (r: L + R)
    :
      𝑤_{cs} (unleftU r) = unleftU r
  .
  Proof.
    unfold unleftU. des_ifs.
    - rewrite wrap_ret. grind.
    - rewrite wrap_triggerUB. unfold triggerUB. grind.
  Qed.

  Lemma wrap_unleftN
        L R (r: L + R)
    :
      𝑤_{cs} (unleftN r) = unleftN r
  .
  Proof.
    unfold unleftN. des_ifs.
    - rewrite wrap_ret. grind.
    - rewrite wrap_triggerNB. unfold triggerNB. grind.
  Qed.

  Lemma wrap_unrightU
        L R (r: L + R)
    :
      𝑤_{cs} (unrightU r) = unrightU r
  .
  Proof.
    unfold unrightU. des_ifs.
    - rewrite wrap_triggerUB. unfold triggerUB. grind.
    - rewrite wrap_ret. grind.
  Qed.

  Lemma wrap_unrightN
        L R (r: L + R)
    :
      𝑤_{cs} (unrightN r) = unrightN r
  .
  Proof.
    unfold unrightN. des_ifs.
    - rewrite wrap_triggerNB. unfold triggerNB. grind.
    - rewrite wrap_ret. grind.
  Qed.

  Lemma wrap_assume
        (P: Prop)
    :
      𝑤_{cs} (assume P) = assume P;;; Ret (tt)
  .
  Proof.
    unfold assume, guarantee.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    des_ifs.
    - rewrite wrap_ret. grind.
    - unfold triggerUB, triggerNB. grind.
      rewrite wrap_bind. rewrite wrap_eventE. grind.
  Qed.

  Lemma wrap_guarantee
        (P: Prop)
    :
      𝑤_{cs} (guarantee P) = guarantee P;;; Ret (tt)
  .
  Proof.
    unfold assume, guarantee.
    repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
    des_ifs.
    - rewrite wrap_ret. grind.
    - unfold triggerUB, triggerNB. grind.
      rewrite wrap_bind. rewrite wrap_eventE. grind.
  Qed.

  Lemma wrap_ext
        R (itr0 itr1: itree _ R)
        (EQ: itr0 = itr1)
    :
      𝑤_{cs} itr0 = 𝑤_{cs} itr1
  .
  Proof. subst; refl. Qed.

End WRAPFACTS.

Global Program Instance wrap_rdb: red_database (mk_box (@wrap_itree)) :=
  mk_rdb
    1
    (mk_box wrap_bind)
    (mk_box wrap_tau)
    (mk_box wrap_ret)
    (mk_box wrap_pE)
    (mk_box wrap_pE)
    (mk_box wrap_callE)
    (mk_box wrap_eventE)
    (mk_box wrap_triggerUB)
    (mk_box wrap_triggerNB)
    (mk_box wrap_unwrapU)
    (mk_box wrap_unwrapN)
    (mk_box wrap_unleftU)
    (mk_box wrap_unleftN)
    (mk_box wrap_unrightU)
    (mk_box wrap_unrightN)
    (mk_box wrap_assume)
    (mk_box wrap_guarantee)
    (mk_box wrap_ext)
.

Ltac my_red_both := try (prw _red_gen 2 0); try (prw _red_gen 1 0).
(* Ltac my_steps := *)
(*   repeat (cbn; try rewrite ! interp_trigger; *)
(*           grind; my_red_both; try (f_equiv; try refl; r; i); *)
(*           try rewrite tau_eutt). *)
Ltac my_steps := repeat (cbn; try rewrite !interp_trigger;
                         try eapply eutt_eq_bind; try refl; ii;
                         grind; resub; my_red_both; try rewrite tau_eutt).

Lemma focus_left_wrap_commute: ∀ R (i: itree Es R) cs,
    (focus_left (𝑤_{cs} i)) ≈ (𝑤_{cs} focus_left i).
Proof.
  i. unfold focus_left, wrap, wrap_itree.
  rewrite ! interp_interp.
  eapply eutt_interp; try refl.
  ii. unfold trivial_Handler. destruct a; my_steps.
  { destruct c; ss.
    my_steps.
    { unfold assume, guarantee, triggerUB, triggerNB. des_ifs; my_steps. }
    { unfold assume, guarantee, triggerUB, triggerNB. des_ifs; my_steps. }
  }
  destruct s; ss.
  { resub. my_steps.
    unfold focus_left_h, unwrapU, triggerUB.
    destruct p; my_steps; des_ifs; my_steps.
  }
  { resub. my_steps. }
Qed.

Lemma focus_right_wrap_commute: ∀ R (i: itree Es R) cs,
    (focus_right (𝑤_{cs} i)) ≈ (𝑤_{cs} focus_right i).
Proof.
  i. unfold focus_right, wrap, wrap_itree.
  rewrite ! interp_interp.
  eapply eutt_interp; try refl.
  ii. unfold trivial_Handler. destruct a; my_steps.
  { destruct c; ss.
    my_steps.
    { unfold assume, guarantee, triggerUB, triggerNB. des_ifs; my_steps. }
    { unfold assume, guarantee, triggerUB, triggerNB. des_ifs; my_steps. }
  }
  destruct s; ss.
  { resub. my_steps.
    unfold focus_right_h, unwrapU, triggerUB.
    destruct p; my_steps; des_ifs; my_steps.
  }
  { resub. my_steps. }
Qed.

Global Program Instance conds_CM: CM.t := {
   car := conds;
}.
Next Obligation.
  econs; ss.
  - unfold equiv, conds_equiv. ii; ss. etrans; et.
Qed.
Next Obligation.
  econs.
  - ii. rr. extensionalities x. unfold oplus, conds_oplus. eapply eps_r.
  - ii. rr. extensionalities x. unfold oplus, conds_oplus. eapply eps_l.
Qed.

(* Opaque MRAS.equiv. *)
Opaque MRA.car.
Let MS := (ModSem_MRA).
Global Program Instance Hoare_WA_ModSem: WA.t (H:=MS.(MRA.equiv)) (S:=conds_CM) | 150 := {
  morph := (𝑤);
}.
Next Obligation.
  i; ss. unfold oplus, OPlus_pointed.
  destruct a, b; ss. cbn.
  rr. ss. esplits; ss. unfold wrap, wrap_fnsems.
  rewrite ! map_app.
  eapply Forall2_app.
  - rewrite ! List.map_map. eapply Forall2_fmap_2.
    eapply Reflexive_instance_0. rr. i; ss. destruct x; ss.
    splits; ss. i.
    my_steps.
    repeat (cbn; try rewrite !interp_trigger; grind; my_red_both; try (f_equiv; try refl; i); try rewrite tau_eutt).
    rewrite focus_left_wrap_commute. refl.
  - rewrite ! map_map. eapply Forall2_fmap_2.
    eapply Reflexive_instance_0. rr. i; ss. destruct x; ss.
    splits; ss. i.
    repeat (cbn; try rewrite !interp_trigger; grind; my_red_both; try (f_equiv; try refl; i); try rewrite tau_eutt).
    rewrite focus_right_wrap_commute. refl.
Qed.
Next Obligation.
  i; ss.
  destruct a; ss. cbn.
  rr. ss. esplits; ss. unfold wrap, wrap_fnsems.
  eapply Forall2_fmap_l.
  eapply Reflexive_instance_0. rr. i; ss. destruct x; ss.
  splits; ss. i. unfold assume, guarantee. grind.
  admit "ez".
Qed.
Next Obligation.
  i; ss.
Qed.
Next Obligation.
  ii. subst. destruct x0, y0; ss. upt. des_ifs.
  unfold wrap in *. ss. unfold wrap in *. destruct t, t0; ss. unfold wrap_modsem_ in *. ss.
  injection Heq; clear Heq. intro T.
  injection Heq0; clear Heq0. intro U.
  subst.
  rr in H0. rr. ss. des. esplits; ss.
  admit "ez".
Qed.

Global Instance itree_Equiv {E R}: Equiv (itree E R) := λ (a b: itree E R), eutt eq a b.
Global Program Instance itree_WrapBar {R}: WrapBarCommute (T:=itree Es R) | 150.
Next Obligation.
  ii. do 2 r. unfold wrap, wrap_itree. unfold bar, itree_Bar.
  rewrite ! interp_interp. eapply eutt_interp; try refl.
  ii. unfold trivial_Handler. destruct a0; ss.
  { destruct c. my_steps.
    - unfold guarantee, assume, triggerUB, triggerNB. des_ifs; my_steps.
    - unfold guarantee, assume, triggerUB, triggerNB. des_ifs; my_steps.
  }
  destruct s0; ss.
  { my_steps. destruct p; my_steps.
    - unfold core_h. unfold triggerUB. my_steps.
    - unfold core_h. unfold triggerUB. my_steps.
  }
  { destruct e; my_steps. }
Qed.

Global Program Instance ModSem_WrapBar: WrapBarCommute (T:=ModSem.t) | 150.
Next Obligation.
  i. rr. des_ifs. unfold wrap in *. ss.
  injection Heq0; intro T; clear Heq0.
  injection Heq1; intro U; clear Heq1.
  subst. destruct t; ss. cbn. hnf. esplits; ss.
  unfold wrap. eapply Forall2_fmap. eapply Forall2_fmap.
  eapply Reflexive_instance_0.
  - ii. des_ifs. ss.
    unfold map_snd in *. des_ifs. unfold wrap, wrap_ktree in *. ss. clarify. esplits; ss.
    i. unfold bar, ktree_Bar. unfold bar, itree_Bar.
    unfold guarantee, assume, triggerUB, triggerNB. des_ifs; my_steps.
    { change (interp (case_ trivial_Handler (case_ core_h trivial_Handler)) (i x)) with ( |i x| ).
      change (interp (case_ trivial_Handler (case_ core_h trivial_Handler)) (wrap_itree s (i x))) with ( |𝑤_{s} (i x)| ).
      rewrite wrap_bar. refl.
    }
    des_ifs; my_steps.
Qed.
