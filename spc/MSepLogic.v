Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import PCM.
Require Import Any.
Require Import ITreelib.
Require Import AList.
Require Import Coq.Init.Decimal.
Require Export IProp.

Set Implicit Arguments.

From iris.bi Require Import derived_connectives updates.
From iris.prelude Require Import options.
From iris.proofmode Require Export tactics.
Require Export DisableSsreflect.
Arguments Z.of_nat: simpl nomatch.


Create HintDb iprop.
Ltac uipropall :=
  repeat (autounfold with iprop; autorewrite with iprop;
       all_once_fast ltac:(fun H => autounfold with iprop in H; autorewrite with iprop in H); ss).

Variable Mod: Type.
Variable ctxref: list Mod -> list Mod -> Prop.
Variable Stb: Type.
Variable add: Stb -> Stb -> Stb.
Variable unit: Stb.
Variable wrap: (Stb * Mod) -> Mod.
Hypothesis add_assoc: forall a b c, (add (add a b) c) = add a (add b c).
Hypothesis add_comm: forall a b, (add a b) = (add b a).
Hypothesis unit_id: forall x, add x unit = x.
Context `{PRE: PreOrder _ ctxref}.
Hypothesis hcomp: forall a b c d, ctxref a b -> ctxref c d -> ctxref (a ++ c) (b ++ d).
Hypothesis ctxref_comm: forall a b, ctxref (a ++ b) (b ++ a).
Hypothesis ctxref_assoc: forall a b c, ctxref (a ++ (b ++ c)) ((a ++ b) ++ c).
Hypothesis mod_affine: forall a, ctxref [a] [].

Variable core: Mod -> Mod.
Hypothesis core_spec: forall a, ctxref [a] ([a] ++ [core a]).
Hypothesis core_idem: forall a, core (core a) = core a.
(* Hypothesis core_mono: forall a b, exists c, core (a b) = add (core a) c. *)

Lemma ctxref_assoc_rev: forall a b c, ctxref ((a ++ b) ++ c) (a ++ (b ++ c)).
Proof.
  i. etrans. { eapply ctxref_comm. } rewrite ctxref_assoc.
  rewrite ctxref_comm. rewrite ctxref_assoc. rewrite ctxref_comm. refl.
Qed.

Lemma mods_affine: forall a, ctxref a [].
Proof.
  induction a; ss.
  { refl. }
  { etrans; et. change a0 with ([] ++ a0) at 2. rewrite cons_app. eapply hcomp.
    - eapply mod_affine.
    - refl.
  }
Qed.

Definition add2 (s0: Stb) (sm: list (Stb * Mod)): list (Stb * Mod) :=
  (map (fun '(s, m) => (add s s0, m)) sm)
.

Lemma unit_id2: forall x, add2 unit x = x.
  { i. unfold add2. rewrite <- map_id. f_equal. extensionality sm. des_ifs. rewrite unit_id. ss. }
Qed.

Require Import Permutation.
Notation "(≡)" := (Permutation).
Notation "A ≡ B" := (Permutation A B).

Lemma app_Permutation_assoc X (p q r: list X): (p ++ q) ++ r ≡ p ++ (q ++ r).
Proof.
  revert q r. induction p; i; ss.
  rewrite IHp. ss.
Qed.

Lemma ctxref_perm: forall a b, a ≡ b -> ctxref a b.
Proof.
  i. induction H.
  { refl. }
  { rewrite cons_app. erewrite cons_app with (xtl:=l'). eapply hcomp; et. refl. }
  { change (y :: x :: l) with ([y] ++ [x] ++ l).
    change (x :: y :: l) with ([x] ++ [y] ++ l).
    rewrite ctxref_comm.
    rewrite ctxref_assoc_rev. eapply hcomp; try refl.
    rewrite ctxref_comm. eapply hcomp; try refl.
  }
  { etrans; et. }
Qed.

Global Program Instance ctxref_perm_Proper: Proper ((≡) ==> (≡) ==> eq) ctxref.
Next Obligation.
  ii. eapply Axioms.prop_ext. split; i.
  - etrans. { eapply ctxref_perm. sym. et. } etrans; et. eapply ctxref_perm; et.
  - etrans. 2: { eapply ctxref_perm. sym. et. } etrans; et. eapply ctxref_perm; et.
Qed.

Global Program Instance ctxref_perm_Proper2: Proper ((≡) ==> (≡) ==> impl) ctxref.
Next Obligation.
  ii.
  - etrans. { eapply ctxref_perm. sym. et. } etrans; et. eapply ctxref_perm; et.
Qed.

Global Program Instance ctxref_perm_Proper3: Proper ((≡) ==> (≡) ==> (flip impl)) ctxref.
Next Obligation.
  ii.
  - etrans. 2: { eapply ctxref_perm. sym. et. } etrans; et. eapply ctxref_perm; et.
Qed.


Module HARDER.
  (* Definition mProp := list Mod. *)
  (* Definition mProp := (Stb * (list Mod -> Prop))%type. *)
  Definition mPred := (list (Stb * Mod) -> Prop)%type.

  Record mProp :=
    mProp_intro {
        mProp_pred :> mPred;
        (* mProp_perm: forall r0 r1 (LE: r0 ≡ r1), mProp_pred r0 -> mProp_pred r1; *)
        mProp_perm :> Proper ((≡) ==> (flip impl)) mProp_pred;
      }.
  Arguments mProp_intro: clear implicits.

  Program Definition Sepconj (P Q: mProp): mProp :=
    mProp_intro (fun m => exists a b, m ≡ a ++ b /\ (P: mPred) a /\ (Q: mPred) b) _.
  Next Obligation.
    ii. ss. des. clarify. esplits; et. etrans; [|et]. ss.
  Qed.

  Program Definition Pure (P: Prop): mProp := mProp_intro (fun _ => P) _.

  Program Definition Ex {X: Type} (P: X -> mProp): mProp := mProp_intro (fun sm => exists x, (P x: mPred) sm) _.
  Next Obligation.
    ii. ss. des. esplits; et. eapply mProp_perm; et.
  Qed.

  Program Definition Univ {X: Type} (P: X -> mProp): mProp := mProp_intro (fun sm => forall x, (P x: mPred) sm) _.
  Next Obligation.
    ii. ss. des. esplits; et. eapply mProp_perm; et.
  Qed.

  Program Definition Own (m0: list (Stb * Mod)): mProp := mProp_intro (fun sm => m0 ≡ sm) _. (* sublist m0 sm. *)
  Next Obligation.
    ii. ss. etrans; et. sym; ss.
  Qed.

  Definition OwnM (m0: list Mod): mProp := Own (map (pair unit) m0).

  Program Definition Wrp (s0: Stb) (P: mProp): mProp :=
    mProp_intro (fun sm => exists sm0, sm ≡ add2 s0 sm0 /\ (P: mPred) sm0) _.
  Next Obligation.
    ii. ss. des. esplits; et. etrans; [|et]. et.
  Qed.

  Definition Entails (P Q : mProp) : Prop := (forall sm0, (P: mPred) sm0 -> (Q: mPred) sm0).

  Program Instance Entails_PreOrder: PreOrder Entails.
  Next Obligation. ii. ss. Qed.
  Next Obligation. ii. eapply H0; ss. eapply H; ss. Qed.

  Program Definition Wand (P Q: mProp): mProp :=
    mProp_intro (fun sm => forall smp, (P: mPred) smp -> (Q: mPred) (sm ++ smp)) _
  .
  Next Obligation.
    ii. ss. eapply mProp_perm; [|eapply H0]; et. eapply Permutation_app; et.
  Qed.

  Program Definition And (P Q : mProp) : mProp :=
    mProp_intro (fun sm0 => (P: mPred) sm0 /\ (Q: mPred) sm0) _
  .
  Next Obligation.
    ii. ss. des. esplits; eapply mProp_perm; et.
  Qed.

  (*** Refining ***)
  Program Definition Ref (Q: mProp): mProp :=
    mProp_intro (fun tgt => exists src, (Q: mPred) src /\ (forall x, ctxref (map wrap (add2 x tgt)) (map wrap (add2 x src)))) _
  .
  Next Obligation.
    ii. ss. des. esplits; et. ii. etrans; et. eapply ctxref_perm; et. unfold add2. rewrite ! map_map.
    f_equiv. ss.
  Qed.

  Lemma ref_mono: forall P Q, Entails P Q -> Entails (Ref P) (Ref Q).
  Proof.
    unfold Ref, Entails, Wrp, add2. ii; ss. des. esplits; eauto.
  Qed.

  Lemma ref_intro: forall P, Entails P (Ref P).
  Proof.
    unfold Ref, Entails, Wrp, add2. ii; ss. esplits; eauto.
    i. erewrite f_equal; try refl.
  Qed.

  Lemma ref_elim: forall P, Entails (Ref (Ref P)) (Ref P).
  Proof.
    unfold Ref, Entails, Wrp, add2. ii; ss. des. esplits; eauto.
    i. specialize (H0 x). specialize (H1 x). etrans; eauto.
  Qed.

  (*** ref is like an update modality ***)
  Lemma ref_frame: forall P Q, Entails (Sepconj Q (Ref P)) (Ref (Sepconj Q P)).
  Proof.
    unfold Ref, Entails, Wrp, add2, Sepconj. ii; ss. des. subst. exists (a ++ src). esplits; eauto.
    i. specialize (H2 x). rewrite H. rewrite ! map_map. rewrite ! map_app. eapply hcomp; try refl.
    rewrite <- map_map. etrans; et. rewrite map_map. refl.
  Qed.

  (*** ref-wrp-comm ***)
  Lemma ref_wrp: forall s0 P, Entails (Wrp s0 (Ref P)) (Ref (Wrp s0 P)).
  Proof.
    unfold Ref, Entails, Wrp, add2. ii; ss. des. esplits; try refl; eauto.
    i. specialize (H1 (add s0 x)).
    rewrite H.
    rp; et.
    - rewrite ! map_map. do 2 f_equal. extensionality sm. des_ifs. f_equal. rewrite add_assoc. f_equal.
    - rewrite ! map_map. do 2 f_equal. extensionality sm. des_ifs. f_equal. rewrite add_assoc. f_equal.
  Qed.

  Definition Refines (P Q: mProp): Prop := Entails P (Ref Q).

  Definition Emp := Pure True.

  Theorem Ref_Absorbing: forall P, Entails (Sepconj Emp (Ref P)) (Ref P).
  Proof.
    unfold Sepconj, Entails, Pure, Ref. ii; ss. des. clarify. esplits; et. ii. etrans; et.
    unfold add2. rewrite ! map_map. rewrite H. rewrite map_app.
    rewrite <- app_nil_l.
    eapply hcomp; try refl.
    eapply mods_affine.
  Qed.

  Theorem Emp_spec: forall P, Entails P Emp.
  Proof. ii. ss. Qed.

  Theorem adequacy: forall x y, Refines (Own x) (Own y) -> ctxref (map wrap x) (map wrap y).
  Proof.
    ii.
    rr in H. exploit H; eauto.
    { rr. refl. }
    intro T; des.
    specialize (T0 unit).
    rewrite ! unit_id2 in *.
    rr in T. rewrite T. ss.
  Qed.



  (*** wrp-elim ***)
  Lemma wrp_elim: forall s0 s1 P, Entails (Wrp s0 (Wrp s1 P)) (Wrp (add s0 s1) P).
  Proof.
    unfold Refines, Ref, Entails, Wrp, add2. ii; ss. des. subst. esplits; eauto.
    etrans; et. rewrite H0. rewrite ! map_map.
    erewrite f_equal; try refl. repeat f_equal. extensionality sm. des_ifs.
    rewrite add_assoc. f_equal. f_equal. rewrite add_comm. ss.
  Qed.

  (*** wrp-intro ***)
  Lemma wrp_intro: forall P, Entails P (Wrp unit P).
  Proof.
    unfold Entails, Wrp. ii; ss. esplits; eauto. rewrite unit_id2. ss.
  Qed.

  (*** wrp-mono ***)
  Lemma wrp_mono: forall s0 P Q, Entails P Q -> Entails (Wrp s0 P) (Wrp s0 Q).
  Proof.
    unfold Refines, Ref, Entails, Wrp, add2. ii; ss. des. subst.
    exploit H; eauto.
  Qed.

  (*** wrp-mono-ref ***)
  Corollary wrp_mono_ref: forall s0 P Q, Refines P Q -> Refines (Wrp s0 P) (Wrp s0 Q).
  Proof.
    i. red. red. i. eapply wrp_mono in H0; eauto. eapply ref_wrp; eauto.
  Qed.

  Lemma Sep_mono: forall P P' Q Q', Entails P Q -> Entails P' Q' -> Entails (Sepconj P P') (Sepconj Q Q').
  Proof.
    unfold Entails, Sepconj. ii; ss. des. esplits; et.
  Qed.

  Lemma Sep_emp1: forall P, Entails P (Sepconj Emp P).
  Proof.
    unfold Entails, Sepconj, Emp. ii; ss. des. esplits; et.
    { rewrite app_nil_l. ss. }
  Qed.

  Lemma Sep_emp2: forall P, Entails P (Sepconj P Emp).
  Proof.
    unfold Entails, Sepconj, Emp. ii; ss. des. esplits; et.
    { rewrite app_nil_r. ss. }
  Qed.

  Lemma Sep_comm: forall P Q, Entails (Sepconj P Q) (Sepconj Q P).
  Proof.
    unfold Entails, Sepconj, Emp. ii; ss. des. esplits; revgoals; try eassumption. etrans; et.
    rewrite app_Permutation_comm. ss.
  Qed.

  Lemma Sep_assoc: forall P Q R, Entails (Sepconj (Sepconj P Q) R) (Sepconj P (Sepconj Q R)).
  Proof.
    unfold Entails, Sepconj, Emp. ii; ss. des. esplits; revgoals; try eassumption; try refl.
    rewrite H. rewrite H0.
    rewrite app_Permutation_assoc; ss.
  Qed.

  Lemma Wand_intro_r: forall P Q R : mProp, Entails (Sepconj P Q) R -> Entails P (Wand Q R).
  Proof.
    unfold Entails, Sepconj, Wand. ii; ss. eapply H; et.
  Qed.

  Lemma Wand_elim_l: forall P Q R : mProp, Entails P (Wand Q R) -> Entails (Sepconj P Q) R.
  Proof.
    unfold Entails, Sepconj, Wand. ii; ss. des; subst. eapply mProp_perm; et.
  Qed.

  (* bi_persistently *)
  Program Definition Pers (P: mProp): mProp :=
    mProp_intro (fun sm => (P: mPred) (map (fun sm => (sm.1, core sm.2)) sm)) _
  .
  Next Obligation.
    ii; ss. eapply mProp_perm; [|et]. rewrite H. ss.
  Qed.

  Lemma Pers_mono: forall P Q, Entails P Q -> Entails (Pers P) (Pers Q).
  Proof.
    unfold Entails, Pers. ii. eauto.
  Qed.

  Lemma Pers_idemp_2: forall P, Entails (Pers P) (Pers (Pers P)).
  Proof.
    unfold Entails, Pers. ii; ss. rewrite map_map.
    erewrite f_equal; et. f_equal. extensionality x. destruct x; ss. rewrite core_idem. ss.
  Qed.

  Lemma Pers_emp_2: Entails Emp (Pers Emp).
  Proof.
    unfold Entails, Pers, Pure. ii. ss.
  Qed.

  Lemma Pers_and_2: forall P Q, Entails (And (Pers P) (Pers Q)) (Pers (And P Q)).
  Proof.
    unfold Entails, Pers, And. ii. ss.
  Qed.

  Lemma Pers_exists_1: forall A (Ψ: A -> mProp), Entails (Pers (Ex Ψ)) (Ex (Pers ∘ Ψ)).
  Proof.
    unfold Entails, Pers, Ex. ii. ss.
  Qed.

  (* Lemma Pers_and_sep_elim: forall P Q, Entails (And (Pers P) Q) (Sepconj P Q). *)
  (* Proof. *)
  (*   unfold Entails, Pers, And, Sepconj. ii; ss. des. esplits; eauto. *)
  (* Qed. *)

  (* Lemma Pers_absorbing: forall P Q, Entails (Sepconj (Pers P) Q) (Pers P). *)
  (* Proof. *)
  (*   unfold Entails, Pers, Sepconj. ii; ss. des. eapply mProp_perm; [|et]. rewrite H. rewrite map_app. *)
  (* Qed. *)

  Definition PersR: mProp -> mProp := Ref ∘ Pers.

  Lemma PersR_Absorbing: forall P Q, Entails (Sepconj (PersR P) Q) (PersR P).
  Proof.
    intros.
    etrans.
    2: { eapply Ref_Absorbing. }
    etrans.
    2: { eapply Sep_comm. }
    eapply Sep_mono; et.
    { refl. }
    { eapply Emp_spec. }
  Qed.

  Lemma PersR_and_sep_elim: forall P Q, Entails (And (Pers P) Q) (Sepconj P Q).
  Proof.
    unfold Entails, Pers, And, Sepconj. ii; ss. des. esplits; eauto.
  Qed.


    bi_mixin_persistently_absorbing : ∀ P Q : PROP, bi_entails (bi_sep (bi_persistently P) Q) (bi_persistently P);
    bi_mixin_persistently_and_sep_elim : ∀ P Q : PROP, bi_entails (bi_and (bi_persistently P) Q) (bi_sep P Q) }.
  (*** TODO: Trivial Rules about Pure, Ex, Univ, And, Or, etc... ***)

End HARDER.
