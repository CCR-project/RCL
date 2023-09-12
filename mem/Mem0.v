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

  Lemma affine_aux: ∀ sk0 sk1 (EQV: Sk.extends sk0 sk1) (WF: Sk.wf sk1),
      ModSemPair.sim (MemSem sk0) (MemSem sk1).
  Proof.
    i. ss.
    econs.
    { instantiate (1:=top2). ss. }
    2: { instantiate (2:=unit).
         instantiate (1:=fun _ '(st_src, st_tgt) =>
                           exists m0 m1, st_tgt = Any.upcast m0 /\ st_src = Any.upcast m1 /\ mem_extends m1 m0).
         ss. esplits; ss; et.
         r. esplits; ss. i. uo. des_ifs_safe.
         rr in EQV. des. rr in EQV. unfold oplus, Sk.add in *. ss. rr in WF.
         erewrite alist_permutation_find.
         2: { et. }
         2: { sym; et. }
         erewrite alist_find_app; et. ss.
    }
    ss. ii. des; ss; clarify.
    {
      esplits; ss; et. ii. des; subst.
      rr in SIMMRS1. des.
      eapply sim_itree_fsubset with []; ss.
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
    {
      esplits; ss; et. ii. des; subst.
      rr in SIMMRS1. des.
      eapply sim_itree_fsubset with []; ss.
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
    {
      esplits; ss; et. ii. des; subst.
      rr in SIMMRS1. des.
      eapply sim_itree_fsubset with []; ss.
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
    {
      esplits; ss; et. ii. des; subst.
      rr in SIMMRS1. des.
      eapply sim_itree_fsubset with []; ss.
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
    {
      esplits; ss; eauto 10. ii. des; subst.
      assert(W:=extends_valid_ptr SIMMRS1).
      rr in SIMMRS1. des.
      eapply sim_itree_fsubset with []; ss.
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

  Lemma sim_strong_bar: ∀ a b, ModSemPair.sim a b -> ModSemPair.sim ( |a| ) ( |b| ).
  Proof.
    i. upt. des_ifs; ss. inv H.
    unshelve econs; et.
    i. unfold bar, ModSem.bar in FINDS. ss. rewrite in_map_iff in *. des.
    destruct x; ss. clarify.
    hexploit sim_fnsems; et. intro T; des.
    esplits; et.
    { rewrite in_map_iff. esplits; et. ss. }
    clear - SIM. ii. subst. exploit SIM; et. instantiate (1:=y). intro T.
    unfold bar, ktree_Bar, bar, itree_Bar.
    abstr (i y) i_src.
    abstr (f_tgt y) i_tgt.
    clear_tac.
    revert T.
    clear Heqitr_src. 
    ss.
  Qed.

  Fixpoint sim_str (n: nat): ModSem.t -> ModSem.t -> Prop :=
    match n with
    | 0 => λ a b, ModSemPair.sim a b
    | S n => λ a b, sim_str n ( |a| ) ( |b| ) ∧ ∀ s, sim_str n (𝑤_{s} a) (𝑤_{s} b)
    end
  .

  Lemma sim_str_intro
    (IHB: ∀ a b, ModSemPair.sim a b -> ModSemPair.sim ( |a| ) ( |b| ))
    (IHW: ∀ a b, ModSemPair.sim a b -> ∀ s, ModSemPair.sim ( 𝑤_{s} a ) ( 𝑤_{s} b ))
    a b
    (BASE: ModSemPair.sim a b)
    :
    ∀ n, sim_str n a b.
  Proof.
    i. gen a b. induction n; i; ss.
    esplits; et.
  Qed.

  Lemma sim_str_ref_str: ∀ a b, (∀ n, sim_str n a b) -> b ⊑S a.
  Proof.
    ii. gen a b. induction n; i; ss.
    { eapply ModSemPair.adequacy; et. eapply (H 0). }
    esplits; et.
    - eapply IHn; et. i. specialize (H (S n0)). ss. des; et.
    - i. eapply IHn; et. i. specialize (H (S n0)). ss. des; et.
  Qed.

  Local Opaque MemSem.
  Lemma affine_aux2: ∀ n, ∀ sk0 sk1 (EQV: Sk.extends sk0 sk1) (WF: Sk.wf sk1),
      sim_str n (MemSem sk0) (MemSem sk1).
  Proof.
    induction n; i.
    { eapply affine_aux; et. }
    ss. esplits; ss.
    admit "tt".
    admit "tt".
  Qed.
  Local Transparent MemSem.



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
    i; cbn.
    ii. induction n.
    { eapply ModSemPair.adequacy.
      eapply affine_aux; ss.
    }
    Local Opaque MemSem.
    ss.
    split; ss.
    -
      ss.
    econs.
    { instantiate (1:=top2). ss. }
    2: { instantiate (2:=unit).
         instantiate (1:=fun _ '(st_src, st_tgt) =>
                           exists m0 m1, st_tgt = Any.upcast m0 /\ st_src = Any.upcast m1 /\ mem_extends m1 m0).
         ss. esplits; ss; et.
         r. esplits; ss. i. uo. des_ifs_safe.
         rr in EQV. des. rr in EQV. unfold oplus, Sk.add in *. ss. rr in WF.
         erewrite alist_permutation_find.
         2: { et. }
         2: { sym; et. }
         erewrite alist_find_app; et. ss.
    }
    ss. ii. des; ss; clarify.
    {
      esplits; ss; et. ii. des; subst.
      rr in SIMMRS1. des.
      eapply sim_itree_fsubset with []; ss.
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
    {
      esplits; ss; et. ii. des; subst.
      rr in SIMMRS1. des.
      eapply sim_itree_fsubset with []; ss.
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
    {
      esplits; ss; et. ii. des; subst.
      rr in SIMMRS1. des.
      eapply sim_itree_fsubset with []; ss.
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
    {
      esplits; ss; et. ii. des; subst.
      rr in SIMMRS1. des.
      eapply sim_itree_fsubset with []; ss.
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
    {
      esplits; ss; eauto 10. ii. des; subst.
      assert(W:=extends_valid_ptr SIMMRS1).
      rr in SIMMRS1. des.
      eapply sim_itree_fsubset with []; ss.
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
    }
    {
      ss.
    }
  Qed.
  Next Obligation.
    i; cbn.
    eapply bar_state_irr; ss.
  Qed.

End PROOF.
