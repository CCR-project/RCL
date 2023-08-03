Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export ModSemE.
Require Export AList.
Require Import Skeleton.
Require Import STS Behavior.
Require Import Any.
Require Import Permutation.
Require Import ModSem.
Require Import SimModSem.
Require Import SimGlobal.

Set Implicit Arguments.




Section MOD.

  Context `{Sk.ld}.

  (* Theorem add_cref_proper: forall ctx md0 md1, md0 ⊑ md1 -> (ctx ⊕ md0) ⊑ (ctx ⊕ md1). *)
  (* Proof. *)
  (*   ii. ss. *)
  (* Qed. *)

  (* Program Instance add_cref_Proper0: Proper ((⊑) ==> eq ==> (⊑)) ((⊕)). *)
  (* Next Obligation. *)
  (*   ii. subst. *)
  (* Qed. *)

  Theorem add_comm
    md0 md1
    :
    (md0 ⊕ md1) ⊑ (md1 ⊕ md0)
  .
  Proof.
    eapply ModPair.adequacy.
    econs; eauto.
    2: { ii; ss. rewrite Sk.add_comm. refl. }
    ii; ss.
    econs.
    { instantiate (1:=top2). ss. }
    2: { instantiate (2:=unit).
         instantiate (1:=fun _ '(st_src, st_tgt) => exists st0 st1, st_tgt = Any.pair st0 st1 /\ st_src = Any.pair st1 st0).
         ss. esplits; et. ss. }
    ss.
    eapply Forall2_app.
    -
    -
    ii.
  Qed.

End MOD.

Section ModSem.

  Context {CONF: EMSConfig}.

  Let add_comm_aux
      ms0 ms1 stl0 str0
      P
      (SIM: stl0 = str0)
    :
      <<COMM: Beh.of_state (ModSem.compile (ms0 ⊕ ms1) P) stl0
              <1=
              Beh.of_state (ModSem.compile (ms1 ⊕ ms0) P) str0>>
  .
  Proof.
    subst. revert str0. pcofix CIH. i. pfold.
    punfold PR. induction PR using Beh.of_state_ind; ss.
    - econs 1; et.
    - econs 2; et.
      clear CIH. clear_tac. revert st0 H.
      pcofix CIH. i. punfold H0. pfold.
      inv H0.
      + econs 1; eauto. ii. ss. exploit STEP; et. i; des. right. eapply CIH; et. pclearbot. ss.
      + econs 2; eauto. des. esplits; eauto. right. eapply CIH; et. pclearbot. ss.
    - econs 4; et. pclearbot. right. eapply CIH; et.
    - econs 5; et. rr in STEP. des. rr. esplits; et.
    - econs 6; et. ii. exploit STEP; et. i; des. clarify.
  Qed.

  Lemma wf_comm
        ms0 ms1
    :
      <<EQ: ModSem.wf (ms0 ⊕ ms1) = ModSem.wf (ms1 ⊕ ms0)>>
  .
  Proof.
    assert (forall ms0 ms1, ModSem.wf (ModSem.add ms0 ms1) -> ModSem.wf (ModSem.add ms1 ms0)).
    { i. inv H. econs; ss.
      { rewrite List.map_app in *.
        eapply nodup_comm; et. rewrite ! List.map_map in *. unfold map_snd in *. rp; et.
        - eapply List.map_ext; ss. i. des_ifs; ss.
        - eapply List.map_ext; ss. i. des_ifs; ss.
      }
    }
    r. eapply prop_ext. split; i; auto.
  Qed.

  Theorem add_comm
          ms0 ms1 (P0 P1: Prop) (IMPL: P1 -> P0)
          (WF: ModSem.wf (ms1 ⊕ ms0))
    :
      <<COMM: Beh.of_program (ModSem.compile (ms0 ⊕ ms1) (Some P0)) <1= Beh.of_program (ModSem.compile (ms1 ⊕ ms0) (Some P1))>>
  .
  Proof.
    destruct (classic (P1)); cycle 1.
    { ii. eapply initial_itr_not_wf; et. }
    replace P0 with P1.
    2: { eapply prop_ext. split; auto. }
    ii. ss. r in PR. r. eapply add_comm_aux; et.
    assert((prog (add ms1 ms0)) ⩯ (prog (add ms0 ms1))).
    {
      ii. destruct a; ss. f_equiv; try refl.
    }
    erewrite beh_eutt_irr; et. ss. unfold initial_itr. f_equiv; try refl. i. des_u.
    f_equiv; try refl.
    f_equiv; try refl.
    f_equiv; try refl.
    - f_equiv; try refl.
  Qed.

  Theorem add_comm
          ms0 ms1 (P0 P1: Prop) (IMPL: P1 -> P0)
    :
      <<COMM: Beh.of_program (compile (add ms0 ms1) (Some P0)) <1= Beh.of_program (compile (add ms1 ms0) (Some P1))>>
  .
  Proof.
    destruct (classic (P1)); cycle 1.
    { ii. eapply initial_itr_not_wf; et. }
    replace P0 with P1.
    2: { eapply prop_ext. split; auto. }
    ii. ss. r in PR. r. eapply add_comm_aux; et.
    rp; et. clear PR. ss. cbn. unfold initial_itr. f_equal.
    { extensionality u. destruct u. f_equal.
      replace (@interp_Es Any.t (prog (add ms1 ms0))) with (@interp_Es Any.t (prog (add ms0 ms1))).
      { f_equal.
        { ss. f_equal. f_equal. eapply alist_permutation_find.
          { inv WF. et. }
          { eapply Permutation_app_comm. }
        }
        { unfold initial_p_state. extensionality mn. ss.
          erewrite alist_permutation_find; et.
          { inv WF. ss. }
          { eapply Permutation_app_comm. }
        }
      }
      f_equal. unfold prog. extensionality T. extensionality e. destruct e.
      f_equal. f_equal. symmetry. eapply alist_permutation_find; et.
      { inv WF. ss. }
      { eapply Permutation_app_comm. }
    }
  Qed.

  Lemma add_assoc' ms0 ms1 ms2:
    add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
  Proof.
    induction ms2; ss. unfold add. f_equal; ss.
    { eapply app_assoc. }
    { eapply app_assoc. }
  Qed.

  Lemma add_assoc_eq ms0 ms1 ms2
    :
      add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
  Proof.
    unfold add. ss. f_equal.
    { apply List.app_assoc. }
    { apply List.app_assoc. }
  Qed.

  Theorem add_assoc
          ms0 ms1 ms2 P
    :
      <<COMM: Beh.of_program (compile (add ms0 (add ms1 ms2)) P) <1=
              Beh.of_program (compile (add (add ms0 ms1) ms2) P)>>
  .
  Proof.
    rewrite add_assoc_eq. ss.
  Qed.

  Theorem add_assoc_rev
          ms0 ms1 ms2 P
    :
      <<COMM: Beh.of_program (compile (add ms0 (add ms1 ms2)) P) <1=
              Beh.of_program (compile (add (add ms0 ms1) ms2) P)>>
  .
  Proof.
    rewrite add_assoc_eq. ss.
  Qed.





  Theorem add_comm
          md0 md1
    :
      <<COMM: Beh.of_program (compile (add md0 md1)) <1= Beh.of_program (compile (add md1 md0))>>
  .
  Proof.
    ii. unfold compile in *.
    destruct (classic (ModSemL.wf (enclose (add md1 md0)) /\ Sk.wf (sk (add md1 md0)))).
    2: { eapply ModSemL.initial_itr_not_wf. ss. }
    ss. des. assert (SK: Sk.wf (Sk.add (sk md0) (sk md1))).
    { apply Sk.wf_comm. auto. }
    rewrite Sk.add_comm; et.
    eapply ModSemL.add_comm; [| |et].
    { i. split; auto. unfold enclose. ss. rewrite Sk.add_comm; et.
      inv H2. inv H3. econs; ss.
      { rewrite List.map_app in *. eapply nodup_comm; et. }
      { rewrite List.map_app in *. eapply nodup_comm; et. }
    }
    { rewrite Sk.add_comm; et. }
  Qed.

  Lemma add_assoc' ms0 ms1 ms2:
    add ms0 (add ms1 ms2) = add (add ms0 ms1) ms2.
  Proof.
    unfold add. f_equal.
    { extensionality skenv_link. ss. apply ModSemL.add_assoc'. }
    { ss. rewrite Sk.add_assoc. auto. }
  Qed.

  Theorem add_assoc
          md0 md1 md2
    :
      <<COMM: Beh.of_program (compile (add md0 (add md1 md2))) =
              Beh.of_program (compile (add (add md0 md1) md2))>>
  .
  Proof.
    rewrite add_assoc'. ss.
  Qed.

  Theorem add_assoc_rev
          md0 md1 md2
    :
      <<COMM: Beh.of_program (compile (add (add md0 md1) md2)) =
              Beh.of_program (compile (add md0 (add md1 md2)))>>
  .
  Proof.
    rewrite add_assoc'. ss.
  Qed.





 
   Lemma add_list_snoc
         x xs
     :
       (add_list (snoc xs x)) = (ModL.add (add_list xs) x)
   .
   Proof.
     ginduction xs; ii; ss.
     { cbn. rewrite ModL.add_empty_l. rewrite ModL.add_empty_r. refl. }
     { cbn. rewrite <- ModL.add_assoc'. f_equal. rewrite <- IHxs. refl. }
   Qed.

   Lemma add_list_app
         xs ys
     :
       add_list (xs ++ ys) = ModL.add (add_list xs) (add_list ys)
   .
   Proof.
     (* unfold add_list. rewrite map_app. rewrite fold_right_app. *)
     ginduction xs; ii; ss.
     - cbn. rewrite ModL.add_empty_l. refl.
     - rewrite ! add_list_cons. rewrite <- ModL.add_assoc'. f_equal. eapply IHxs; ss.
   Qed.




Section REFINE.
  Context `{Sk.ld}.

   Definition refines {CONF: EMSConfig} (md_tgt md_src: ModL.t): Prop :=
     (* forall (ctx: list Mod.t), Beh.of_program (ModL.compile (add_list (md_tgt :: ctx))) <1= *)
     (*                           Beh.of_program (ModL.compile (add_list (md_src :: ctx))) *)
     forall (ctx: list Mod.t), Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) md_tgt)) <1=
                               Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) md_src))
   .

   Definition refines_strong (md_tgt md_src: ModL.t): Prop :=
     forall {CONF: EMSConfig}, refines md_tgt md_src.

   Section CONF.
   Context {CONF: EMSConfig}.

   Definition refines2 (md_tgt md_src: list Mod.t): Prop :=
     forall (ctx: list Mod.t), Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) (Mod.add_list md_tgt))) <1=
                               Beh.of_program (ModL.compile (ModL.add (Mod.add_list ctx) (Mod.add_list md_src)))
   .

   Global Program Instance refines2_PreOrder: PreOrder refines2.
   Next Obligation.
     ii. ss.
   Qed.
   Next Obligation.
     ii. eapply H0 in PR. eapply H1 in PR. eapply PR.
   Qed.

   (*** vertical composition ***)
   Global Program Instance refines_PreOrder: PreOrder refines.
   Next Obligation. ii. ss. Qed.
   Next Obligation. ii. eapply H1. eapply H0. ss. Qed.

   Global Program Instance refines_strong_PreOrder: PreOrder refines_strong.
   Next Obligation. ii. ss. Qed.
   Next Obligation. ii. eapply H1. eapply H0. ss. Qed.



   (*** horizontal composition ***)
   Theorem refines_add
         (md0_src md0_tgt md1_src md1_tgt: Mod.t)
         (SIM0: refines md0_tgt md0_src)
         (SIM1: refines md1_tgt md1_src)
     :
       <<SIM: refines (ModL.add md0_tgt md1_tgt) (ModL.add md0_src md1_src)>>
   .
   Proof.
     ii. r in SIM0. r in SIM1.
     (***
ctx (a0 b0)
(ctx a0) b0
(ctx a0) b1
      ***)
     rewrite ModL.add_assoc in PR.
     specialize (SIM1 (snoc ctx md0_tgt)). spc SIM1. rewrite Mod.add_list_snoc in SIM1. eapply SIM1 in PR.
     (***
ctx (a0 b1)
(a0 b1) ctx
a0 (b1 ctx)
(b1 ctx) a0
      ***)
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     (***
(b1 ctx) a1
a1 (b1 ctx)
(a1 b1) ctx
ctx (a1 b1)
      ***)
     specialize (SIM0 (cons md1_src ctx)). spc SIM0. rewrite Mod.add_list_cons in SIM0. eapply SIM0 in PR.
     eapply ModL.add_comm in PR.
     rewrite ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     ss.
   Qed.

   Theorem refines_proper_r
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines (ModL.add (Mod.add_list mds0_tgt) (Mod.add_list ctx)) (ModL.add (Mod.add_list mds0_src) (Mod.add_list ctx))>>
   .
   Proof.
     ii. r in SIM0. rename ctx into xs. rename ctx0 into ys.
     (***
ys + (tgt + xs)
(tgt + xs) + ys
tgt + (xs + ys)
(xs + ys) + tgt
      ***)
     eapply ModL.add_comm in PR.
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     (***
(xs + ys) + src
src + (xs + ys)
(src + xs) + ys
ys + (src + xs)
      ***)
     specialize (SIM0 (xs ++ ys)). spc SIM0. rewrite Mod.add_list_app in SIM0. eapply SIM0 in PR.
     eapply ModL.add_comm in PR.
     rewrite ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     ss.
   Qed.

   Theorem refines_proper_l
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_tgt)) (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_src))>>
   .
   Proof.
     ii. r in SIM0. rename ctx into xs. rename ctx0 into ys.
     (***
ys + (xs + tgt)
(ys + xs) + tgt
(ys + xs) + src
ys + (xs + src)
      ***)
     rewrite ModL.add_assoc' in PR.
     specialize (SIM0 (ys ++ xs)). spc SIM0. rewrite Mod.add_list_app in SIM0. eapply SIM0 in PR.
     rewrite <- ModL.add_assoc' in PR.
     ss.
   Qed.

   Definition refines_closed (md_tgt md_src: ModL.t): Prop :=
     Beh.of_program (ModL.compile md_tgt) <1= Beh.of_program (ModL.compile md_src)
   .

   Global Program Instance refines_closed_PreOrder: PreOrder refines_closed.
   Next Obligation. ii; ss. Qed.
   Next Obligation. ii; ss. eapply H1. eapply H0. eauto. Qed.

   Lemma refines_close: refines <2= refines_closed.
   Proof. ii. specialize (PR nil). ss. unfold Mod.add_list in *. ss. rewrite ! ModL.add_empty_l in PR. eauto. Qed.

   (*** horizontal composition ***)
   Theorem refines2_add
         (s0 s1 t0 t1: list Mod.t)
         (SIM0: refines2 t0 s0)
         (SIM1: refines2 t1 s1)
     :
       <<SIM: refines2 (t0 ++ t1) (s0 ++ s1)>>
   .
   Proof.
     ii. r in SIM0. r in SIM1.
     (***
ctx (a0 b0)
(ctx a0) b0
(ctx a0) b1
      ***)
     rewrite Mod.add_list_app in PR.
     rewrite ModL.add_assoc in PR.
     specialize (SIM1 (ctx ++ t0)). spc SIM1. rewrite Mod.add_list_app in SIM1. eapply SIM1 in PR.
     (***
ctx (a0 b1)
(a0 b1) ctx
a0 (b1 ctx)
(b1 ctx) a0
      ***)
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     rewrite <- ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     (***
(b1 ctx) a1
a1 (b1 ctx)
(a1 b1) ctx
ctx (a1 b1)
      ***)
     specialize (SIM0 (s1 ++ ctx)). spc SIM0. rewrite Mod.add_list_app in SIM0. eapply SIM0 in PR.
     eapply ModL.add_comm in PR.
     rewrite ModL.add_assoc' in PR.
     eapply ModL.add_comm in PR.
     rewrite ! Mod.add_list_app in *.
     assumption.
   Qed.


   Corollary refines2_pairwise
             (mds0_src mds0_tgt: list Mod.t)
             (FORALL: List.Forall2 (fun md_src md_tgt => refines2 [md_src] [md_tgt]) mds0_src mds0_tgt)
     :
       refines2 mds0_src mds0_tgt.
   Proof.
     induction FORALL; ss.
     hexploit refines2_add.
     { eapply H0. }
     { eapply IHFORALL. }
     i. ss.
   Qed.

   Lemma refines2_eq (mds0 mds1: list Mod.t)
     :
       refines2 mds0 mds1 <-> refines (Mod.add_list mds0) (Mod.add_list mds1).
   Proof.
     split.
     { ii. eapply H0. auto. }
     { ii. eapply H0. auto. }
   Qed.

   Lemma refines2_app mhd0 mhd1 mtl0 mtl1
         (HD: refines2 mhd0 mhd1)
         (TL: refines2 mtl0 mtl1)
     :
       refines2 (mhd0++mtl0) (mhd1++mtl1).
   Proof.
     eapply refines2_eq. rewrite ! Mod.add_list_app. etrans.
     { eapply refines_proper_l. eapply refines2_eq. et. }
     { eapply refines_proper_r. eapply refines2_eq. et. }
   Qed.

   Lemma refines2_cons mhd0 mhd1 mtl0 mtl1
         (HD: refines2 [mhd0] [mhd1])
         (TL: refines2 mtl0 mtl1)
     :
       refines2 (mhd0::mtl0) (mhd1::mtl1).
   Proof.
     eapply (refines2_app HD TL).
   Qed.

   End CONF.



   (*** horizontal composition ***)
   Theorem refines_strong_add
         (md0_src md0_tgt md1_src md1_tgt: Mod.t)
         (SIM0: refines_strong md0_tgt md0_src)
         (SIM1: refines_strong md1_tgt md1_src)
     :
       <<SIM: refines_strong (ModL.add md0_tgt md1_tgt) (ModL.add md0_src md1_src)>>
   .
   Proof.
     intros CONF. eapply (@refines_add CONF); et.
   Qed.

   Theorem refines_strong_proper_r
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines_strong (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines_strong (ModL.add (Mod.add_list mds0_tgt) (Mod.add_list ctx)) (ModL.add (Mod.add_list mds0_src) (Mod.add_list ctx))>>
   .
   Proof.
     intros CONF. eapply (@refines_proper_r CONF); et.
   Qed.

   Theorem refines_strong_proper_l
         (mds0_src mds0_tgt: list Mod.t) (ctx: list Mod.t)
         (SIM0: refines_strong (Mod.add_list mds0_tgt) (Mod.add_list mds0_src))
     :
       <<SIM: refines_strong (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_tgt)) (ModL.add (Mod.add_list ctx) (Mod.add_list mds0_src))>>
   .
   Proof.
     intros CONF. eapply (@refines_proper_l CONF); et.
   Qed.

   Lemma refines_strong_refines {CONF: EMSConfig}: refines_strong <2= refines.
   Proof. ii. eapply PR; et. Qed.
End REFINE.

