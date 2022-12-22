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
Hypothesis mod_affine: forall a, ctxref [a] [].

Variable core: Mod -> Mod.
Hypothesis core_spec: forall a, ctxref [a] ([a] ++ [core a]).
Hypothesis core_idem: forall a, core (core a) = core a.
(* Hypothesis core_mono: forall a b, exists c, core (a b) = add (core a) c. *)

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



Module HARDER.
  (* Definition mProp := list Mod. *)
  (* Definition mProp := (Stb * (list Mod -> Prop))%type. *)
  Definition mProp := (list (Stb * Mod) -> Prop)%type.

  Definition Sepconj (P Q: mProp): mProp := (fun m => exists a b, m = a ++ b /\ P a /\ Q b).

  Definition Pure (P: Prop): mProp := fun _ => P.

  Definition Ex {X: Type} (P: X -> mProp): mProp := fun sm => exists x, P x sm.

  Definition Univ {X: Type} (P: X -> mProp): mProp := fun sm => forall x, P x sm.

  Definition Own (m0: list (Stb * Mod)): mProp := fun sm => m0 = sm. (* sublist m0 sm. *)
  Definition OwnM (m0: list Mod): mProp := Own (map (pair unit) m0).

  Definition Wrp (s0: Stb) (P: mProp): mProp := fun sm => exists sm0, sm = add2 s0 sm0 /\ P sm0.

  Definition Entails (P Q : mProp) : Prop :=
    forall sm0, P sm0 -> Q sm0
  .

  Definition Wand (P Q: mProp): mProp :=
    fun sm => forall smp, P smp -> Q (sm ++ smp)
  .

  Definition And (P Q : mProp) : mProp :=
    fun sm0 => P sm0 /\ Q sm0
  .

  (*** Refining ***)
  Definition Ref (Q: mProp): mProp :=
    fun tgt => exists src, Q src /\ (forall x, ctxref (map wrap (add2 x tgt)) (map wrap (add2 x src)))
  .

  Lemma ref_mono: forall P Q, Entails P Q -> Entails (Ref P) (Ref Q).
  Proof.
    unfold Ref, Entails, Wrp, add2. ii. des. esplits; eauto.
  Qed.

  Lemma ref_intro: forall P, Entails P (Ref P).
  Proof.
    unfold Ref, Entails, Wrp, add2. ii. esplits; eauto.
    i. erewrite f_equal; try refl.
  Qed.

  Lemma ref_elim: forall P, Entails (Ref (Ref P)) (Ref P).
  Proof.
    unfold Ref, Entails, Wrp, add2. ii. des. esplits; eauto.
    i. specialize (H0 x). specialize (H1 x). etrans; eauto.
  Qed.

  (*** ref is like an update modality ***)
  Lemma ref_frame: forall P Q, Entails (Sepconj Q (Ref P)) (Ref (Sepconj Q P)).
  Proof.
    unfold Ref, Entails, Wrp, add2, Sepconj. ii. des. subst. esplits; eauto.
    i. specialize (H2 x). rewrite ! map_app. eapply hcomp; eauto.
    { refl. }
  Qed.

  (*** ref-wrp-comm ***)
  Lemma ref_wrp: forall s0 P, Entails (Wrp s0 (Ref P)) (Ref (Wrp s0 P)).
  Proof.
    unfold Ref, Entails, Wrp, add2. ii. des. subst. esplits; eauto.
    i. specialize (H1 (add s0 x)).
    rp; et.
    - rewrite ! map_map. do 2 f_equal. extensionality sm. des_ifs. f_equal. rewrite add_assoc. f_equal.
    - rewrite ! map_map. do 2 f_equal. extensionality sm. des_ifs. f_equal. rewrite add_assoc. f_equal.
  Qed.

  Definition Refines (P Q: mProp): Prop := Entails P (Ref Q).

  Theorem Ref_Absorbing: forall P, Entails (Sepconj (Pure True) (Ref P)) (Ref P).
  Proof.
    unfold Sepconj, Entails, Pure, Ref. ii. des. clarify. esplits; et. ii. etrans; et.
    unfold add2. rewrite ! map_map. rewrite map_app.
    rewrite <- app_nil_l.
    eapply hcomp; try refl.
    eapply mods_affine.
  Qed.

  Theorem affine: forall P, Refines P (Pure True).
  Proof.
    ii. unfold Ref. exists []. esplits; ss. i. eapply mods_affine.
  Qed.

  Theorem adequacy: forall x y, Refines (Own x) (Own y) -> ctxref (map wrap x) (map wrap y).
  Proof.
    ii.
    rr in H. exploit H; eauto.
    { rr. refl. }
    intro T; des.
    specialize (T0 unit).
    rewrite ! unit_id2 in *.
    rr in T. subst. ss.
  Qed.



  (*** wrp-elim ***)
  Lemma wrp_elim: forall s0 s1 P, Entails (Wrp s0 (Wrp s1 P)) (Wrp (add s0 s1) P).
  Proof.
    unfold Refines, Ref, Entails, Wrp, add2. ii. des. subst. esplits; eauto.
    rewrite ! map_map.
    erewrite f_equal; try refl. repeat f_equal. extensionality sm. des_ifs.
    rewrite add_assoc. f_equal. f_equal. rewrite add_comm. ss.
  Qed.

  (*** wrp-intro ***)
  Lemma wrp_intro: forall P, Entails P (Wrp unit P).
  Proof.
    unfold Entails, Wrp. ii. esplits; eauto. rewrite unit_id2. ss.
  Qed.

  (*** wrp-mono ***)
  Lemma wrp_mono: forall s0 P Q, Entails P Q -> Entails (Wrp s0 P) (Wrp s0 Q).
  Proof.
    unfold Refines, Ref, Entails, Wrp, add2. ii. des. subst.
    exploit H; eauto.
  Qed.

  (*** wrp-mono-ref ***)
  Corollary wrp_mono_ref: forall s0 P Q, Refines P Q -> Refines (Wrp s0 P) (Wrp s0 Q).
  Proof.
    i. red. red. i. eapply wrp_mono in H0; eauto. eapply ref_wrp; eauto.
  Qed.


  Definition Emp := Pure True.

  Lemma Sep_mono: forall P P' Q Q', Entails P Q -> Entails P' Q' -> Entails (Sepconj P P') (Sepconj Q Q').
  Proof.
    unfold Entails, Sepconj. ii. des. esplits; et.
  Qed.

  Lemma Sep_emp1: forall P, Entails P (Sepconj Emp P).
  Proof.
    unfold Entails, Sepconj, Emp. ii. des. esplits; et.
    { rewrite app_nil_l. ss. }
    { ss. }
  Qed.

  Lemma Sep_emp2: forall P, Entails P (Sepconj P Emp).
  Proof.
    unfold Entails, Sepconj, Emp. ii. des. esplits; et.
    { rewrite app_nil_r. ss. }
    { ss. }
  Qed.

  Lemma Sep_comm: forall P Q, Entails (Sepconj P Q) (Sepconj Q P).
  Proof.
    unfold Entails, Sepconj, Emp. ii. des. subst. esplits. try eassumption. et.
    { rewrite app_nil_r. ss. }
    { ss. }
  Qed.

    bi_mixin_sep_comm' : ∀ P Q : PROP, bi_entails (bi_sep P Q) (bi_sep Q P);
    bi_mixin_sep_assoc' : ∀ P Q R : PROP, bi_entails (bi_sep (bi_sep P Q) R) (bi_sep P (bi_sep Q R));

  Lemma Wand_intro_r: forall P Q R : mProp, Entails (Sepconj P Q) R -> Entails P (Wand Q R).
  Proof.
    unfold Entails, Sepconj, Wand. ii. eapply H; et.
  Qed.

  Lemma Wand_elim_l: forall P Q R : mProp, Entails P (Wand Q R) -> Entails (Sepconj P Q) R.
  Proof.
    unfold Entails, Sepconj, Wand. ii. des; subst. eapply H; et.
  Qed.

  (* bi_persistently *)
  Definition Pers (P: mProp): mProp :=
    fun sm => P (map (fun '(s, m) => (s, core m)) sm)
  .

  Lemma Pers_mono: forall P Q, Entails P Q -> Entails (Pers P) (Pers Q).
  Proof.
    unfold Entails, Pers. ii. eauto.
  Qed.

  Lemma Pers_idemp_2: forall P, Entails (Pers P) (Pers (Pers P)).
  Proof.
    unfold Entails, Pers. ii. rewrite map_map.
    erewrite f_equal; et. f_equal. extensionality x. des_ifs. rewrite core_idem. ss.
  Qed.

  Lemma Pers_emp_2: Entails (Pure True) (Pers (Pure True)).
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

  (* Lemma Pers_absorbing: forall P Q, Entails (Sepconj (Pers P) Q) (Pers P). *)
  (* Proof. *)
  (*   unfold Entails, Pers, Sepconj. ii. des. clarify. *)
  (* Qed. *)

  (* Lemma Pers_and_sep_elim: forall P Q, Entails (And (Pers P) Q) (Sepconj P Q). *)
  (* Proof. *)
  (*   unfold Entails, Pers, And, Sepconj. ii. des. esplits; eauto. *)
  (* Qed. *)

  Definition PersR: mProp -> mProp := Ref ∘ Pers.

  Lemma Pers_absorbing: forall P Q, Entails (Sepconj (PersR P) Q) (PersR P).
  Proof.
    intros.
    replace (PersR P) with (Sepconj (PersR P) (Pure True)); cycle 1.
    { extensionality x. eapply Axioms.prop_ext. split; i.
      - r. eapply Ref_Absorbing. eapply Sepconj_comm.
        unfold Sepconj, Pure.
        des; clarify. r. unfold PersR, Ref in *. des. esplits; et. ii. etrans; et.
        Entails P (Ref (Pure True))
        Entails P (Ref Q)
    eapply affine.
    unfold Entails, PersR, Pers, Sepconj. ii. des. clarify.
  Qed.

  Lemma Pers_and_sep_elim: forall P Q, Entails (And (Pers P) Q) (Sepconj P Q).
  Proof.
    unfold Entails, Pers, And, Sepconj. ii. des. esplits; eauto.
  Qed.


    bi_mixin_persistently_absorbing : ∀ P Q : PROP, bi_entails (bi_sep (bi_persistently P) Q) (bi_persistently P);
    bi_mixin_persistently_and_sep_elim : ∀ P Q : PROP, bi_entails (bi_and (bi_persistently P) Q) (bi_sep P Q) }.
  (*** TODO: Trivial Rules about Pure, Ex, Univ, And, Or, etc... ***)

End HARDER.
