Require Import Coqlib Mod ModSem Algebra Any Skeleton AList.
From stdpp Require Import base gmap.

Set Implicit Arguments.

Record _cond: Type := mk_cond {
    meta: Type;
    precond: meta -> Any.t -> Prop;
    postcond: meta -> Any.t -> Prop;
}.

Definition cond := pointed _cond.

Global Instance cond_ops: OPlus _cond :=
  fun c0 c1 =>
    mk_cond
      (fun m => c0.(precond) m.1 /1\ c1.(precond) m.2)
      (fun m => c0.(postcond) m.1 /1\ c1.(postcond) m.2)
.

Global Instance cond_equiv: Equiv _cond :=
  fun c0 c1 =>
    exists (p: path c0.(meta) c1.(meta)),
      <<PRE: ∀ m0 z, c0.(precond) m0 z <-> c1.(precond) (p.(to) m0) z>> ∧
      <<POST: ∀ m0 z, c0.(postcond) m0 z <-> c1.(postcond) (p.(to) m0) z>>
.

Global Program Instance _cond_EquivFacts: EquivFacts (T:=_cond).
Next Obligation.
  econs.
  - ii. rr. exists (path_id _). ss.
  - ii. rr. rr in H. des. exists (path_sym p). ss. esplits; ss.
    + i. rewrite PRE. rewrite correct2. ss.
    + i. rewrite POST. rewrite correct2. ss.
  - ii. rr. rr in H. des. rr in H0. des. exists (path_trans p p0). ss. esplits; ss.
    + i. rewrite PRE. rewrite PRE0. ss.
    + i. rewrite POST. rewrite POST0. ss.
Qed.

Global Program Instance cond_EquivFacts: EquivFacts (T:=cond).
Next Obligation.
  econs.
  - ii. upt. des_ifs; refl.
  - ii. upt. des_ifs; sym.
  - ii. upt. des_ifs; etrans; et.
Qed.

Global Program Instance _cond_OPlusFacts: OPlusFacts (T:=_cond).
Next Obligation.
  i. rr. destruct a, b; ss.
  exists (path_comm _ _). ss. esplits; i; ss; split; i; des; ss.
Qed.
Next Obligation.
  i. rr. destruct a, b; ss.
  exists (path_assoc _ _ _). ss. esplits; i; ss; split; i; des; ss.
Qed.
Next Obligation.
  ii. rr in H. rr in H0. des.
  rr. exists (path_combine p0 p). ss. esplits; i; ss; split; i; des; ss;
    esplits; ss; et; try apply PRE0; try apply PRE; try apply POST0; try apply POST; ss.
Qed.

Global Program Instance cond_OPlusFacts: OPlusFacts (T:=cond).
Next Obligation.
  ii. upt. des_ifs; ss. eapply oplus_comm.
Qed.
Next Obligation.
  ii. upt. des_ifs; ss. eapply oplus_assoc.
Qed.
Next Obligation.
  ii. upt. des_ifs; ss. setoid_subst. refl.
Qed.

Global Program Instance cond_EpsFacts: EpsFacts (T:=cond).
Next Obligation.
  ii. rr. des_ifs; ss.
  (* eexists (path_unitr _); ss. *)
  (* split; ii; ss. *)
  (* - destruct m0; des_u. ss. split; i; des; ss. *)
  (* - destruct m0; des_u. ss. split; i; des; ss. *)
Qed.
Next Obligation.
  ii. rr. des_ifs; ss.
  (* eexists (path_unitl _); ss. *)
  (* split; ii; ss. *)
  (* - destruct m0; des_u. ss. split; i; des; ss. *)
  (* - destruct m0; des_u. ss. split; i; des; ss. *)
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

Global Instance conds_equiv: Equiv conds := fun c0 c1 => ∀ fn, c0 fn ≡ c1 fn.

Global Program Instance conds_EquivFacts: EquivFacts (T:=conds).
Next Obligation.
  econs.
  - ii. refl.
  - ii. sym; et.
  - ii. etrans; et.
Qed.

Global Program Instance conds_OPlusFacts: OPlusFacts (T:=conds).
Next Obligation.
  ii. unfold oplus, conds_oplus. rewrite oplus_comm. ss.
Qed.
Next Obligation.
  ii. unfold oplus, conds_oplus. rewrite oplus_assoc. ss.
Qed.
Next Obligation.
  ii. unfold oplus, conds_oplus. do 2 r in H. do 2 r in H0.
  rewrite H. rewrite H0. ss.
Qed.



Section WRAP.

  Definition wrap_h (cs: conds): Handler callE Es :=
    fun _ ce =>
      match ce with
      | Call fn arg =>
          let c := (cs fn) in
          match c with
          | mytt => trigger (Call fn arg)
          | just c => m <- trigger (Choose (c.(meta)));;
                      guarantee(c.(precond) m arg);;;
                      ret <- trigger (Call fn arg);;
                      assume(c.(postcond) m ret);;;
                      Ret ret
          end
      end
  .

  Global Instance wrap_itree {R}: Wrap conds (itree Es R) :=
    fun cs itr => interp (case_ (bif:=sum1) (wrap_h cs) trivial_Handler) itr
  .

  Global Instance wrap_ktree: Wrap conds (string * (Any.t -> itree Es Any.t)) :=
    fun cs nf =>
      (nf.1, fun arg =>
               let c := (cs nf.1) in
               match c with
               | mytt => nf.2 arg
               | just c =>
                   m <- trigger (Choose (c.(meta)));;
                   assume(c.(precond) m arg);;;
                   ret <- 𝑤_{cs} (nf.2 arg);;
                   guarantee(c.(postcond) m ret);;;
                   Ret ret
               end)
  .

  Global Instance wrap_fnsems: Wrap conds (alist string (Any.t -> itree Es Any.t)) :=
    fun cs nfs => List.map (fun nf => 𝑤_{cs} nf) nfs
  .

  Context `{Sk.ld}.

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

  Global Program Instance wrap_mod: Wrap conds (Mod.t) :=
    fun cs md => Mod.mk (fun sk => 𝑤_{cs} (md.(Mod.get_modsem) sk)) md.(Mod.sk) _ _ _.
  Next Obligation.
    i. ss. erewrite Mod.get_modsem_Proper; et.
  Qed.
  Next Obligation.
    i. ss. admit "strengthen".
  Qed.
  Next Obligation.
    i. ss. admit "strengthen".
  Qed.

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

  Lemma wrap_assume
        (P: Prop)
    :
      𝑤_{cs} (assume P) = assume P;;; tau;; Ret (tt)
  .
  Proof.
    unfold assume.
    repeat (try rewrite wrap_bind; try rewrite bind_bind). grind.
    rewrite wrap_eventE.
    repeat (try rewrite wrap_bind; try rewrite bind_bind). grind.
    rewrite wrap_ret.
    refl.
  Qed.

  Lemma wrap_guarantee
        (P: Prop)
    :
      𝑤_{cs} (guarantee P) = guarantee P;;; tau;; Ret (tt)
  .
  Proof.
    unfold guarantee.
    repeat (try rewrite wrap_bind; try rewrite bind_bind). grind.
    rewrite wrap_eventE.
    repeat (try rewrite wrap_bind; try rewrite bind_bind). grind.
    rewrite wrap_ret.
    refl.
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
    (mk_box wrap_assume)
    (mk_box wrap_guarantee)
    (mk_box wrap_ext)
.

Ltac my_red_both := try (prw _red_gen 2 0); try (prw _red_gen 1 0).
Ltac my_steps :=
  repeat (cbn; try rewrite ! interp_trigger;
          grind; my_red_both; try (f_equiv; try refl; r; i);
          try rewrite tau_eutt).

Lemma focus_left_wrap_commute: ∀ R (i: itree Es R) cs,
    (focus_left (𝑤_{cs} i)) ≈ (𝑤_{cs} focus_left i).
Proof.
  i. unfold focus_left, wrap, wrap_itree.
  rewrite ! interp_interp.
  eapply eutt_interp; try refl.
  ii. unfold trivial_Handler. destruct a; my_steps.
  { destruct c; ss.
    destruct (cs fn) eqn:T; cycle 1.
    { my_steps. }
    my_steps.
    { unfold assume, guarantee. my_steps. }
    { unfold assume, guarantee. my_steps. }
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
    destruct (cs fn) eqn:T; cycle 1.
    { my_steps. }
    my_steps.
    { unfold assume, guarantee. my_steps. }
    { unfold assume, guarantee. my_steps. }
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
  econs.
  - ii; ss. unfold oplus, conds_oplus. unfold eps, conds_eps. rewrite eps_r. refl.
  - ii; ss. unfold oplus, conds_oplus. unfold eps, conds_eps. rewrite eps_l. refl.
Qed.

(* Opaque MRAS.equiv. *)
Opaque MRAS.car.
Let M := (MRA_to_MRAS ModSem_MRA).
Global Program Instance Hoare_WA: @WA.t M conds_CM := {
  morph := (𝑤);
}.
Next Obligation.
  i; ss. unfold oplus, OPlus_pointed.
  destruct a, b; ss. cbn.
  r. eapply hat_Proper. f_equiv.
  rr. ss. esplits; ss. unfold wrap, wrap_fnsems.
  rewrite ! map_app.
  eapply Forall2_app.
  - rewrite ! map_map. eapply Forall2_fmap_2.
    eapply Reflexive_instance_0. rr. i; ss. destruct x; ss.
    splits; ss. i.
    destruct (s s0) eqn:T; cycle 1.
    { refl. }
    my_steps. eapply focus_left_wrap_commute.
  - rewrite ! map_map. eapply Forall2_fmap_2.
    eapply Reflexive_instance_0. rr. i; ss. destruct x; ss.
    splits; ss. i.
    destruct (s s0) eqn:T; cycle 1.
    { refl. }
    my_steps. eapply focus_right_wrap_commute.
Qed.
Next Obligation.
  i; ss.
  destruct a; ss. cbn.
  r. eapply hat_Proper. f_equiv.
  rr. ss. esplits; ss. unfold wrap, wrap_fnsems.
  eapply Forall2_fmap_l.
  eapply Reflexive_instance_0. rr. i; ss. destruct x; ss.
  splits; ss. i. refl.
Qed.
Next Obligation.
  i; ss.
Qed.
Next Obligation.
  assert(T: Proper ((≡) ==> (≡@{ModSem_MRA}) ==> (≡)) (𝑤)).
  {
    ii. rr in H. rr in H0. rr. des_ifs. setoid_subst.
  }
  ii; ss. unfold wrap.
Qed.
