Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From Ordinal Require Import Ordinal Arithmetic.
Require Import SimSTS.

Set Implicit Arguments.


CoInductive conat: Type :=
| O: conat
| S: conat -> conat
.

(*
inf, ?
?, inf
fin & even, fin & even
*)
Variant _is_even (is_even: conat -> conat -> Prop): conat -> conat -> Prop :=
| is_even_O: _is_even is_even O O
| is_even_l: forall n m, is_even n m -> _is_even is_even (S (S n)) m
| is_even_r: forall n m, is_even n m -> _is_even is_even n (S (S m))
.

Definition is_even: _ -> _ -> Prop := paco2 _is_even bot2.

#[global] Hint Constructors _is_even.
Hint Unfold is_even.

Lemma is_even_mon: monotone2 _is_even.
Proof.
  ii. induction IN; ss; eauto.
Qed.

Hint Resolve is_even_mon: paco.

Notation "p -2> q" :=
  (fun x0 x1 => forall (PR: p x0 x1 : Prop), q x0 x1 : Prop)
  (at level 51, right associativity).

Definition _is_evenL (is_even: conat -> conat -> Prop) (n m: conat): Prop :=
  (exists n', n = S (S n') /\ is_even n' m)
.

Definition _is_evenL_cond (n m: conat): Prop := (exists n', n = S (S n')).

Definition is_evenL (is_even: conat -> conat -> Prop) : conat -> conat -> Prop := _is_evenL_cond -2> _is_evenL is_even.

Lemma compat
  :
  is_evenL <*> _is_even <3= _is_even <*> is_evenL
.
Proof.
  ii. unfold compose in *.
  rr in PR.
  (* if x1 is (S O), it does not help here. *)
Abort.

Lemma decompat
  :
  _is_even <*> is_evenL <3= is_evenL <*> _is_even
.
Proof.
  ii. unfold compose in *.
  rr in PR0. des. subst.
  rr. esplits; eauto.
  inv PR; ss.
  (* if n' is not even it does not hold *)
Abort.

(* maybe the theory needs to recognize conditions? *)



Theorem is_evenB_spec2
  r
  :
  paco2 _is_even r <2= is_evenL (upaco2 _is_even r)
.
Proof.
  i. punfold PR. induction PR.
  - ii. rr in PR. des; ss.
  - r in H. des.
    + ii. inv PR. clarify. econs; eauto.
    + ii. inv PR. clarify. econs; eauto.
  - r in H. des.
    + ii. inv PR. r. esplits; eauto. left.
      { revert_until r. pcofix CIH.
        i. punfold H0. inv H0.
        - r in H1. des.
          { pfold. econs; eauto. left. eapply paco2_mon; eauto. }
          { pfold. econs; eauto. }
        - r in H. des.
          { pfold. econs; eauto. }
          { pfold. econs; eauto. right. eapply CIH.
            pfold. econs; eauto. left. admit "??? do we need respectful?".
          }
      }
    + ii. rr in PR. des; subst. rr. esplits; eauto. left. pfold. econs; eauto.
Qed.


