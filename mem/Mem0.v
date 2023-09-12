Require Import Coqlib Algebra.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import Mod ModSem SimModSem ModSemFacts.
Require Import Skeleton.
Require Import SimModSemStrong.

Set Implicit Arguments.
Set Typeclasses Depth 5.




Ltac my_steps :=
  repeat (esplits; my_red_both;
          try (guclo sim_itree_indC_spec; first [apply sim_itree_indC_choose_tgt|apply sim_itree_indC_take_src|econs]; et);
          try (gstep; eapply sim_itree_pput; eauto);
          try (gstep; eapply sim_itree_pget; eauto);
          i; des; ss; subst; et).

Section PROOF.

  Section BODY.
    Context {Es: Type -> Type}.
    Context `{has_pE: pE -< Es}.
    Context `{has_eventE: eventE -< Es}.
    Definition allocF: (list val) -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        `sz: Z <- (pargs [Tint] varg)?;;
        if (Z_le_gt_dec 0 sz && Z_lt_ge_dec (8 * sz) modulus_64)
        then (delta <- trigger (Choose _);;
              let m0': Mem.t := Mem.mem_pad m0 delta in
              let (blk, m1) := Mem.alloc m0' sz in
              trigger (PPut m1↑);;;
              Ret (Vptr (inl blk) 0))
        else triggerUB
    .

    Definition freeF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(b, ofs) <- (pargs [Tptr] varg)?;;
        b <- unleftU b;;
        m1 <- (Mem.free m0 b ofs)?;;
        trigger (PPut m1↑);;;
        Ret (Vint 0)
    .

    Definition loadF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(b, ofs) <- (pargs [Tptr] varg)?;;
        v <- (Mem.load m0 b ofs)?;;
        Ret v
    .

    Definition storeF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(b, ofs, v) <- (pargs [Tptr; Tuntyped] varg)?;;
        m1 <- (Mem.store m0 b ofs v)?;;
        trigger (PPut m1↑);;;
        Ret (Vint 0)
    .

    Definition cmpF: list val -> itree Es val :=
      fun varg =>
        mp0 <- trigger (PGet);;
        m0 <- mp0↓?;;
        '(v0, v1) <- (pargs [Tuntyped; Tuntyped] varg)?;;
        b <- (vcmp m0 v0 v1)?;;
        if b: bool
        then Ret (Vint 1%Z)
        else Ret (Vint 0%Z)
    .

  End BODY.



  Definition MemSem (sk: Sk.t): ModSem.t := Algebra.just
    {|
      ModSem.fnsems := [("alloc", cfunU allocF) ; ("free", cfunU freeF) ; ("load", cfunU loadF) ; ("store", cfunU storeF) ; ("cmp", cfunU cmpF)];
      ModSem.initial_st := (Mem.load_mem sk)↑;
    |}
  .

  Lemma equiv_load_mem: forall sk0 sk1, Sk.wf sk0 -> sk0 ≡ sk1 -> Mem.load_mem sk0 = Mem.load_mem sk1.
  Proof.
    ii. r in H0. unfold Mem.load_mem. f_equiv. extensionalities b ofs.
    uo. des_ifs_safe; ss. destruct b; ss. clarify.
    destruct (alist_find s sk0) eqn:T.
    - erewrite alist_permutation_find in T; et. des_ifs.
    - erewrite alist_permutation_find in T; et. des_ifs.
  Qed.

  Definition mem_extends (m0 m1: Mem.t): Prop :=
    <<BLK: forall b, m0.(Mem.cnts) (inl b) = m1.(Mem.cnts) (inl b)>> /\
    <<NAME: forall fn ofs v, m0.(Mem.cnts) (inr fn) ofs = Some v -> m1.(Mem.cnts) (inr fn) ofs = Some v>> /\
    (* <<CNTS: forall b ofs v, m0.(Mem.cnts) b ofs = Some v -> m1.(Mem.cnts) b ofs = Some v>> /\ *)
    <<NB: m0.(Mem.nb) = m1.(Mem.nb)>>
  .

  Lemma extends_valid_ptr m0 m1: mem_extends m0 m1 ->
                                 forall b ofs, Mem.valid_ptr m0 b ofs = true -> Mem.valid_ptr m1 b ofs = true.
  Proof.
    ii; ss. rr in H. des. unfold Mem.valid_ptr in *. unfold is_some in *. des_ifs.
    exfalso. destruct b; ss; et.
    - erewrite BLK in *; ss. congruence.
    - eapply NAME in Heq0; ss. congruence.
  Qed.

  Definition sim (ms mt: ModSem.t) :=
    match ms, mt with
    | just ms, just mt =>
        exists wf,
        (Forall2 (fun '(fn0, ktr0) '(fn1, ktr1) => fn0 = fn1
                   /\ (sim_fsem (fun (_: unit) => wf) top2 ktr0 ktr1))
           ms.(ModSem.fnsems) mt.(ModSem.fnsems))
        /\ wf (ms.(ModSem.initial_st), mt.(ModSem.initial_st))
    | mytt, mytt => True
    | _, _ => False
    end
  .

  Lemma affine_aux: ∀ sk0 sk1 (EQV: Sk.extends sk0 sk1) (WF: Sk.wf sk1),
      sim (MemSem sk0) (MemSem sk1).
  Proof.
    i. ss.
    unshelve eexists.
    { eapply (fun '(st_src, st_tgt) =>
                           exists m0 m1, st_tgt = Any.upcast m0 /\
                                           st_src = Any.upcast m1 /\ mem_extends m1 m0).
    }
    esplits; ss.
    2: {
      r. esplits; ss. i. uo. des_ifs_safe.
      rr in EQV. des. rr in EQV. unfold oplus, Sk.add in *. ss. rr in WF.
      erewrite alist_permutation_find.
      2: { et. }
      2: { sym; et. }
      erewrite alist_find_app; et. ss.
    }
    econs; [split|]; ss.
    {
      esplits; ss; et. ii. des; subst.
      rr in SIMMRS1. des.
      unfold cfunU, allocF.
      ginit. my_steps.
      destruct (Any.downcast y) eqn:T.
      2: { cbn. unfold triggerUB. my_steps. }
      my_steps. des_ifs; my_steps; unfold triggerUB; my_steps.
      destruct v; my_steps; des_ifs; my_steps; unfold triggerUB; my_steps.
      rr. esplits; ss; et.
      2: { rewrite NB; ss. }
      rr. ss. esplits; try lia.
      - ii. rewrite NB in *. unfold update in *. des_ifs; ss; et.
      - ii. rewrite NB in *. unfold update in *. des_ifs; ss; et.
    }
    econs; [split|]; ss.
    {
      esplits; ss; et. ii. des; subst.
      rr in SIMMRS1. des.
      unfold cfunU, freeF.
      ginit. my_steps.
      destruct (Any.downcast y) eqn:T.
      2: { cbn. unfold triggerUB. my_steps. }
      my_steps. des_ifs; my_steps; unfold triggerUB; my_steps.
      destruct v; my_steps; des_ifs; my_steps; unfold triggerUB; my_steps.
      destruct blk; my_steps; des_ifs; my_steps; unfold triggerUB; my_steps.
      destruct (Mem.free m1 n ofs) eqn:U.
      2: { cbn. unfold triggerUB. my_steps. }
      my_steps.
      unfold Mem.free in *. des_ifs_safe. rewrite <- BLK. des_ifs. my_steps.
      rr. esplits; ss; et.
      rr. ss. esplits; try lia.
      - ii. unfold update in *. des_ifs; ss; et.
      - ii. unfold update in *. des_ifs; ss; et.
    }
    econs; [split|]; ss.
    {
      esplits; ss; et. ii. des; subst.
      rr in SIMMRS1. des.
      unfold cfunU, loadF.
      ginit. my_steps.
      destruct (Any.downcast y) eqn:T.
      2: { cbn. unfold triggerUB. my_steps. }
      my_steps. des_ifs; my_steps; unfold triggerUB; my_steps.
      destruct v; my_steps; des_ifs; my_steps; unfold triggerUB; my_steps.
      destruct (Mem.load m1 blk ofs) eqn:U.
      2: { cbn. unfold triggerUB. my_steps. }
      my_steps.
      assert(V: Mem.load m0 blk ofs = Some v).
      { destruct blk; ss; et. rewrite <- BLK; et. }
      rewrite V; ss. my_steps.
      rr. esplits; ss; et.
    }
    econs; [split|]; ss.
    {
      esplits; ss; et. ii. des; subst.
      rr in SIMMRS1. des.
      unfold cfunU, storeF.
      ginit. my_steps.
      destruct (Any.downcast y) eqn:T.
      2: { cbn. unfold triggerUB. my_steps. }
      my_steps. des_ifs; my_steps; unfold triggerUB; my_steps.
      destruct v; my_steps; des_ifs; my_steps; unfold triggerUB; my_steps.
      destruct (Mem.store m1 blk ofs) eqn:U.
      2: { cbn. unfold triggerUB. my_steps. }
      my_steps.
      unfold Mem.store in *. des_ifs_safe.
      assert(U: Mem.cnts m0 blk ofs = Some v).
      { destruct blk; ss; et. rewrite <- BLK; et. }
      des_ifs. my_steps.
      rr. esplits; ss; et.
      rr. ss. esplits; try lia.
      - ii. extensionalities ofs0. rewrite BLK; ss.
      - ii. des_ifs; ss; et.
    }
    econs; [split|]; ss.
    {
      esplits; ss; eauto 10. ii. des; subst.
      assert(W:=extends_valid_ptr SIMMRS1).
      rr in SIMMRS1. des.
      unfold cfunU, cmpF.
      ginit. my_steps.
      destruct (Any.downcast y) eqn:T.
      2: { cbn. unfold triggerUB. my_steps. }
      my_steps. des_ifs; my_steps; unfold triggerUB; my_steps.
      destruct (vcmp m1 v v0) eqn:U.
      2: { cbn. unfold triggerUB. my_steps. }
      unfold vcmp in *. des_ifs; my_steps; des_ifs; my_steps; rr; esplits; ss;
        bsimpl; des; des_sumbool; ss; subst; exploit W; et; i; try congruence.
      - clear Heq2. exploit W; et; i; try congruence.
      - clear Heq2. exploit W; et; i; try congruence.
    }
  Qed.

  Lemma sim_strong_bar_aux
    wf mrs_src mrs_tgt (i_src i_tgt: itree Es Any.t)
    f_src f_tgt
    (SIM: sim_itree (λ _ : (), wf) top2 f_src f_tgt () (mrs_src, i_src) (mrs_tgt, i_tgt))
    :
    sim_itree (λ _ : (), wf) top2 f_src f_tgt ()
    (mrs_src, bar i_src)
    (mrs_tgt, bar i_tgt)
  .
  Proof.
    ginit.
    revert_until wf.
    gcofix CIH; i.
    punfold SIM. dependent induction SIM using _sim_itree_ind2; my_red_both.
    - gstep. econs; eauto.
    - gstep. econs; eauto. ii. subst. irw. des_u.
      guclo sim_itree_indC_spec. econs; eauto.
      guclo sim_itree_indC_spec. econs; eauto.
      gstep. econsr; et.
      gbase. eapply CIH.
      exploit K; et. intro T. pclearbot. eapply sim_itree_bot_flag_up. eauto.
    - gstep. econs; eauto. ii. subst. irw. des_u.
      guclo sim_itree_indC_spec. econs; eauto.
      guclo sim_itree_indC_spec. econs; eauto.
      gstep. econsr; et.
      gbase. eapply CIH.
      exploit K; et. intro T. pclearbot. eapply sim_itree_bot_flag_up. eauto.
    - gstep. econs; eauto. ii. subst. irw.
      guclo sim_itree_indC_spec. econs; eauto.
      guclo sim_itree_indC_spec. econs; eauto.
      gstep. econsr; et.
      gbase. eapply CIH.
      pclearbot. eapply sim_itree_bot_flag_up. eauto.
    - guclo sim_itree_indC_spec. econs; et.
    - des. guclo sim_itree_indC_spec. econs; et. esplits; et.
      my_steps.
    - my_steps. exploit K; et. intro T; des. eauto.
    - guclo sim_itree_indC_spec. econs; et.
    - my_steps. exploit K; et. intro T; des. eauto.
    - des. guclo sim_itree_indC_spec. econs; et. esplits; et.
      my_steps.
    - unfold core_h. unfold triggerUB. my_steps.
    - unfold core_h. unfold triggerUB. my_steps.
    - gstep. econsr; et.
      { gbase. eapply CIH; eauto. pclearbot. eauto. }
  Qed.

  Lemma sim_strong_bar: ∀ a b, sim a b -> sim ( |a| ) ( |b| ).
  Proof.
    i. upt. des_ifs; ss. des. exists wf. esplits; ss.
    eapply Forall2_apply_Forall2; et.
    clear.
    i. ss. des_ifs. des; ss. clarify. esplits; ss. clear - H0.
    clear - H0. ii. clarify. exploit H0; et. des_u.
    eapply sim_strong_bar_aux; et.
  Qed.

  Require Import WrapModSem.
  Require Import IRed.

  (*** TODO: FIXME ***)
  Global Program Instance wrap_rdb:
    red_database (mk_box (@wrap conds (itree Es Any.t) (@wrap_itree Any.t))) :=
    mk_rdb
      0
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

  Lemma sim_strong_wrap_aux
    wf mrs_src mrs_tgt (i_src i_tgt: itree Es Any.t)
    c
    f_src f_tgt
    (SIM: sim_itree (λ _ : (), wf) top2 f_src f_tgt () (mrs_src, i_src) (mrs_tgt, i_tgt))
    :
    sim_itree (λ _ : (), wf) top2 f_src f_tgt ()
    (mrs_src, 𝑤_{c} i_src)
    (mrs_tgt, 𝑤_{c} i_tgt)
  .
  Proof.
    ginit.
    revert_until wf.
    gcofix CIH; i.
    punfold SIM. dependent induction SIM using _sim_itree_ind2; my_red_both.
    - rewrite ! wrap_ret. gstep. econs; eauto.
    - rewrite ! wrap_bind. rewrite ! wrap_callE.
      unfold wrap_h, guarantee, assume, triggerUB, triggerNB.
      my_red_both. des_ifs; my_steps.
      2: { gstep. econsr; et. i; ss. }
      gstep. econs; eauto. ii. subst. des_u. des_ifs; my_steps.
      2: { gstep. econs; et. i; ss. }
      guclo sim_itree_indC_spec. econs; eauto.
      guclo sim_itree_indC_spec. econs; eauto.
      gstep. econsr; et.
      gbase. eapply CIH.
      exploit K; et. intro T. pclearbot. eapply sim_itree_bot_flag_up. eauto.
    - rewrite ! wrap_bind. rewrite ! wrap_eventE.
      unfold wrap_h, guarantee, assume, triggerUB, triggerNB.
      my_red_both. des_ifs; my_steps.
      gstep. econs; eauto. ii. subst. des_u. des_ifs; my_steps.
      guclo sim_itree_indC_spec. econs; eauto.
      guclo sim_itree_indC_spec. econs; eauto.
      gstep. econsr; et.
      gbase. eapply CIH.
      exploit K; et. intro T. pclearbot. eapply sim_itree_bot_flag_up. eauto.
    - rewrite ! wrap_bind. rewrite ! wrap_eventE.
      unfold wrap_h, guarantee, assume, triggerUB, triggerNB.
      my_red_both. des_ifs; my_steps.
      gstep. econs; eauto. ii. subst. des_ifs; my_steps.
      guclo sim_itree_indC_spec. econs; eauto.
      guclo sim_itree_indC_spec. econs; eauto.
      gstep. econsr; et.
      gbase. eapply CIH.
      pclearbot. eapply sim_itree_bot_flag_up. eauto.
    - rewrite ! wrap_tau. guclo sim_itree_indC_spec. econs; et.
    - rewrite ! wrap_bind. rewrite ! wrap_eventE.
      des. my_steps. guclo sim_itree_indC_spec. econs; et. esplits; et.
      my_steps.
      guclo sim_itree_indC_spec. econs; eauto.
    - my_steps.
      rewrite ! wrap_bind. rewrite ! wrap_eventE.
      des. my_steps. guclo sim_itree_indC_spec. econs; et. i.
      spc K. des.
      my_steps.
      guclo sim_itree_indC_spec. econs; et.
    - rewrite ! wrap_tau. guclo sim_itree_indC_spec. econs; et.
    - my_steps.
      rewrite ! wrap_bind. rewrite ! wrap_eventE.
      des. my_steps. guclo sim_itree_indC_spec. econs; et. i.
      spc K. des.
      my_steps.
      guclo sim_itree_indC_spec. econs; et.
    - rewrite ! wrap_bind. rewrite ! wrap_eventE.
      des. my_steps. guclo sim_itree_indC_spec. econs; et. esplits; et.
      my_steps.
      guclo sim_itree_indC_spec. econs; eauto.
    - rewrite ! wrap_bind. rewrite ! wrap_pE. my_steps.
      gstep. econs; et. my_steps.
      guclo sim_itree_indC_spec. econs; eauto.
      guclo sim_itree_indC_spec. econs; eauto.
      gbase. eapply CIH; et. pclearbot; et.
    - rewrite ! wrap_bind. rewrite ! wrap_pE. my_steps.
      gstep. econs; et. my_steps.
      guclo sim_itree_indC_spec. econs; eauto.
      guclo sim_itree_indC_spec. econs; eauto.
      gbase. eapply CIH; et. pclearbot; et.
    - gstep. econsr; et.
      { gbase. eapply CIH; eauto. pclearbot. eauto. }
  Qed.

  Lemma sim_strong_wrap: ∀ c a b, sim a b -> sim ( 𝑤_{c} a ) ( 𝑤_{c} b ).
  Proof.
    i. destruct a, b; ss. des. exists wf. esplits; ss.
    eapply Forall2_apply_Forall2; et.
    clear.
    i. ss. des_ifs. des; ss. clarify. esplits; ss. clear - H0.
    clear - H0. ii. clarify. exploit H0; et. des_u. i.
    ginit.
    guclo lbindC_spec. econs.
    { unfold assume, guarantee, triggerUB, triggerNB. des_ifs; my_steps.
      - gstep. econs; et.
        instantiate (1:=fun mrs_src' mrs_tgt' _ _ =>
                          mrs_src = mrs_src' /\ mrs_tgt = mrs_tgt'). ss.
      - gstep. econs; et. i; ss.
    }
    i; ss. des; clarify. des_u; ss.
    guclo lbindC_spec. econs.
    { gfinal. right. eapply sim_strong_wrap_aux; et. }
    { i; ss. rr in SIM. des; clarify. des_u; ss.
      unfold assume, guarantee, triggerUB, triggerNB. des_ifs; my_steps.
      - gstep. econs; et.
        rr. esplits; ss.
      - gstep. econsr; et. i; ss.
    }
  Unshelve.
    all: ss.
  Qed.

  Fixpoint sim_str (n: nat): ModSem.t -> ModSem.t -> Prop :=
    match n with
    | 0 => λ a b, sim a b
    | S n => λ a b, sim_str n ( |a| ) ( |b| ) ∧ ∀ s, sim_str n (𝑤_{s} a) (𝑤_{s} b)
    end
  .

  Lemma sim_str_intro
    a b
    (BASE: sim a b)
    :
    ∀ n, sim_str n a b.
  Proof.
    i. gen a b. induction n; i; ss.
    esplits; et.
    { eapply IHn. eapply sim_strong_bar; et. }
    { i. eapply IHn. eapply sim_strong_wrap; et. }
  Qed.

  Lemma sim_str_ref_str: ∀ a b, (∀ n, sim_str n a b) -> b ⊑S a.
  Proof.
    ii. gen a b. induction n; i; ss.
    { eapply ModSemPair.adequacy; et. specialize (H 0). ss.
      rr in H. des_ifs. des; ss.
      econs; et.
      { instantiate (1:=top2); ss. }
      2: { exists tt. instantiate (1:=fun _ => wf). ss. }
      { i. eapply Forall2_In_l in FINDS; et. des. des_ifs. des; clarify.
        esplits; et.
      }
    }
    esplits; et.
    - eapply IHn; et. i. specialize (H (S n0)). ss. des; et.
    - i. eapply IHn; et. i. specialize (H (S n0)). ss. des; et.
  Qed.

  Program Definition Mem: Mod.t := {|
    Mod.get_modsem := MemSem;
    Mod.sk := Sk.unit;
  |}
  .
  Next Obligation.
    ii. r in EQV. unfold MemSem. ss. f_equiv.
    f_equiv. erewrite equiv_load_mem; ss.
  Qed.
  Next Obligation.
    i. eapply sim_str_ref_str. i.
    eapply sim_str_intro. eapply affine_aux; et.
  Qed.

End PROOF.
