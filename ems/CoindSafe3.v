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
inf, inf
fin & even, fin & even
*)
Inductive _is_even (is_even: bool -> bool -> conat -> conat -> Prop): bool -> bool -> conat -> conat -> Prop :=
| is_even_O: forall f_src f_tgt, _is_even is_even f_src f_tgt O O
| is_even_l: forall f_src f_tgt n m, _is_even is_even true f_tgt n m -> _is_even is_even f_src f_tgt (S (S n)) m
| is_even_r: forall f_src f_tgt n m, _is_even is_even f_src true n m -> _is_even is_even f_src f_tgt n (S (S m))
| is_even_progress: forall n m, is_even false false n m -> _is_even is_even true true n m
.
Reset _is_even.

Definition ord: Type := nat * nat.
Definition ord_lt: ord -> ord -> Prop := fun '(ps0, pt0) '(ps1, pt1) => (ps0 < ps1) /\ (pt0 < pt1).
Inductive _is_even (is_even: ord -> ord -> conat -> conat -> Prop): ord -> ord -> conat -> conat -> Prop :=
| is_even_O: forall ps0 pt0 ps1 pt1,
    _is_even is_even (ps0, pt0) (ps1, pt1) O O
| is_even_l: forall ps0 pt0 ps1 pt1 n m,
    _is_even is_even (ps0, pt0) (1 + ps1, pt1) n m ->
    _is_even is_even (ps0, pt0) (ps1, pt1) (S (S n)) m
| is_even_r: forall ps0 pt0 ps1 pt1 n m,
    _is_even is_even (ps0, pt0) (ps1, 1 + pt1) n m ->
    _is_even is_even (ps0, pt0) (ps1, pt1) n (S (S m))
| is_even_progress: forall ps0 pt0 ps1 pt1 n m (LT: ord_lt (ps0, pt0) (ps1, pt1)),
    is_even (ps1, pt1) (ps1, pt1) n m ->
    _is_even is_even (ps0, pt0) (ps1, pt1) n m
.

Definition is_even := paco4 _is_even bot4.

#[global] Hint Constructors _is_even.
Hint Unfold is_even.

Lemma is_even_mon: monotone4 _is_even.
Proof.
  ii. induction IN; ss; eauto.
Qed.
Hint Resolve is_even_mon: paco.

Notation "~4 p" :=
  (fun x0 x1 x2 x3 => ~p x0 x1 x2 x3 : Prop)
    (at level 50, no associativity).

Notation "∧_{ A } B" := (fun _x0 _x1 _x2 _x3 => (forall (a: A), B a _x0 _x1 _x2 _x3)) (at level 50).
Notation "∧_{ a ∈ A } B" := (fun _x0 _x1 _x2 _x3 => (forall (_a: A), (fun a => B) _a _x0 _x1 _x2 _x3)) (at level 50).
Notation "∨_{ A } B" := (fun _x0 _x1 _x2 _x3 => (exists (a: A), B a _x0 _x1 _x2 _x3)) (at level 50).
Notation "∨_{ a ∈ A } B" := (fun _x0 _x1 _x2 _x3 => (exists (_a: A), (fun a => B) _a _x0 _x1 _x2 _x3)) (at level 50).

Section CONT.
  Variable T0 : Type.
  Variable T1 : forall (x0: @T0), Type.
  Variable T2 : forall (x0: @T0) (x1: @T1 x0), Type.
  Variable T3 : forall (x0: @T0) (x1: @T1 x0) (x2: @T2 x0 x1), Type.

  Lemma cup_spec: forall (I: Type) (A: I -> rel4 T0 T1 T2 T3) x, (∨_{I} A <4= x) = (forall i, A i <4= x).
  Proof. i. eapply prop_ext; split; i; des; eauto. Qed.
  Lemma cap_spec: forall (I: Type) (A: I -> rel4 T0 T1 T2 T3) x, (x <4= ∧_{I} A) = (forall i, x <4= A i).
  Proof. i. eapply prop_ext; split; i; des; eauto. Qed.

  (* Definition cont4 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) := *)
  (*   forall A B, gf (A \4/ B) <4= (gf A \4/ gf B). *)

  (* Definition cont4_rev (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) := *)
  (*   forall A B, (gf A \4/ gf B) <4= gf (A \4/ B). *)

  (* Definition tnoc4 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) := *)
  (*   forall A B, (gf A /4\ gf B) <4= gf (A /4\ B). *)

  (* Definition tnoc4_rev (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) := *)
  (*   forall A B, gf (A /4\ B) <4= (gf A /4\ gf B). *)

  Definition cont4 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
    forall I (A: I -> rel4 T0 T1 T2 T3), gf (∨_{I} A) <4= ∨_{I} (gf <*> A).

  Definition cont4_rev (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
    forall I (A: I -> rel4 T0 T1 T2 T3), ∨_{I} (gf <*> A) <4= gf (∨_{I} A).

  Definition tnoc4 (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
    forall I (A: I -> rel4 T0 T1 T2 T3), ∧_{I} (gf <*> A) <4= gf (∧_{I} A).

  Definition tnoc4_rev (gf: rel4 T0 T1 T2 T3 -> rel4 T0 T1 T2 T3) :=
    forall I (A: I -> rel4 T0 T1 T2 T3), gf (∧_{I} A) <4= ∧_{I} (gf <*> A).

  Lemma mono_cont4_rev gf (MON: monotone4 gf): cont4_rev gf.
  Proof. ii. des; eapply MON; eauto. Qed.

  Lemma mono_tnoc4_rev gf (MON: monotone4 gf): tnoc4_rev gf.
  Proof. ii. esplits; eapply MON; eauto; ii; ss; des; eauto. Qed.

  Lemma cont4_tnoc4 gf (CNT: cont4 gf): tnoc4 gf.
  Proof. ii. des. r in CNT. Abort.
End CONT.

Opaque Nat.add.

Lemma is_even_cont: cont4 _is_even.
Proof.
  ii. unfold compose in *. induction PR.
  - admit "unprovable".
  - des; eauto.
  - des; eauto.
  - des; eauto.
Abort.

(* Lemma is_even_tnoc: tnoc4 _is_even. *)
(* Proof. *)
(*   ii. des. *)
(*   induction PR; eauto. *)
(*   - revert PR. revert IHPR. *)
(*     induction PR0; eauto; i. *)
(*     + econs; eauto. eapply IHPR0; eauto. *)
(*       { i. econs; eauto. *)
(*   - des. *)
(*     + left. econs; eauto. *)
(*     + right. econs; eauto. *)
(*   - des. *)
(*     + left. econs; eauto. *)
(*     + right. econs; eauto. *)
(*   - des. *)
(*     + left. econs; eauto. *)
(*     + right. econs; eauto. *)
(* Qed. *)

Notation "p -4> q" :=
  (fun x0 x1 x2 x3 => forall (PR: p x0 x1 x2 x3 : Prop), q x0 x1 x2 x3 : Prop)
  (at level 51, right associativity).

Definition pad A X Y (f: X -> Y): (A -> X) -> (A -> Y) := fun g a => f (g a).

(* Definition _is_evenL (is_even: conat -> conat -> Prop) (n m: conat): Prop := *)
(*   (exists n', n = S (S n') /\ is_even n' m) *)
(* . *)
Definition _is_evenL: (ord -> ord -> conat -> conat -> Prop) -> ord -> ord -> conat -> conat -> Prop :=
  ((∘) ∘ (∘)) (fun is_even n m => exists n', n = S (S n') /\ is_even n' m)
.

(* Definition _is_evenL (is_even: ord -> ord -> conat -> conat -> Prop) (f_src f_tgt: bool) (n m: conat): Prop := *)
(*   (exists n', n = S (S n') /\ is_even true f_tgt n' m) *)
(* . *)

Notation "~4 p" := (fun x0 x1 x2 x3 => ~p x0 x1 x2 x3 : Prop) (at level 50, no associativity).
Definition _is_evenL_cond: (ord -> ord -> conat -> conat -> Prop) := fun _ _ (n m: conat) => (exists n', n = S (S n')).
Definition C0 := (fun rec => _is_evenL_cond /4\ rec).
Definition C1 := (fun rec => (~4 _is_evenL_cond) \4/ rec).

Lemma C0_mon: monotone4 C0.
Proof. ii. unfold C0 in *. des; eauto. Qed.

Lemma C1_mon: monotone4 C1.
Proof. ii. unfold C1 in *. des; eauto. Qed.

Lemma C_adj0: id <5= C1 <*> C0.
Proof.
  ii. unfold compose, id in *. unfold C0, C1 in *.
  destruct (classic (_is_evenL_cond x1 x2 x3 x4)); eauto.
Qed.

Goal C1 <*> C0 <5= id.
Proof.
  ii. unfold compose, id in *. unfold C0, C1 in *.
  des; eauto.
Abort.

Lemma C_adj1: C0 <*> C1 <5= id.
Proof.
  ii. unfold compose, id in *. unfold C0, C1 in *. des; eauto. tauto.
Qed.

Goal forall x y, C0 x <4= y <-> x <4= C1 y.
Proof.
  split; i.
  - eapply C_adj0 in PR. eapply C1_mon; eauto.
  - eapply C_adj1. eapply C0_mon; eauto.
Qed.

Lemma is_evenL_mon: monotone4 _is_evenL.
Proof. ii. r in IN. r. des; eauto. Qed.

Lemma is_evenL_tnoc: tnoc4 _is_evenL.
Proof.
  ii. unfold compose in *. eapply is_evenL_mon; eauto. ii. eauto.
Abort.

Lemma is_evenL_cont: cont4 _is_evenL.
Proof.
  ii. unfold compose in *. r in PR. des. subst. esplits; eauto. econs; eauto.
Qed.

Lemma decompat
  :
  _is_even <*> _is_evenL <5= _is_evenL <*> _is_even
.
Proof.
  ii. unfold compose in *.
  induction PR.
  - admit "unprovable".
  (* N := O : conat *)
  (* M := O : conat *)
Abort.

Definition _is_evenL2: (ord -> ord -> conat -> conat -> Prop) -> ord -> ord -> conat -> conat -> Prop :=
  ((∘) ∘ (∘)) (fun is_even n m => <<LEFT: exists n', n = S (S n') /\ is_even n' m>> \/ <<BASE: n = O /\ m = O>>)
.

Lemma decompat
  :
  _is_even <*> _is_evenL2 <5= _is_evenL2 <*> _is_even
.
Proof.
  ii. unfold compose in *.
  (* set (N:=x3). set (M:=x4). *)
  induction PR.
  - r. eauto.
  - r in IHPR. des; subst.
    + r. left. esplits; eauto.
    + r. left. esplits; eauto.
  - r in IHPR. des; subst.
    + r. left. esplits; eauto.
    + r. right. esplits; eauto. admit "no".
  (* N := O : conat *)
  (* M := S (S O) : conat *)
  - r in H. des; subst.
    + r. left. esplits; eauto.
    + r. right. esplits; eauto.
Abort.

Goal (_is_evenL2 <*> _is_even) (fun _ _ n m => n = O /\ m = S (S O)) (0,0) (0,0) O (S (S O)) <0=
       (_is_even <*> _is_evenL2) (fun _ _ n m => n = O /\ m = S (S O)) (0,0) (0,0) O (S (S O)).
Proof.
  ii. unfold compose in *. r in PR. des; clarify.
Qed.

Lemma decompat
  :
  C0 /5\ _is_even <*> _is_evenL <5= _is_evenL <*> _is_even
.
Proof.
  ii. unfold C0 in *. unfold compose in *. des. rename x0 into rr.
  (* revert PR. *)
  induction PR0; i; r in PR; des; clarify.
  - r. esplits; et. admit "??".
Abort.

Lemma decompat
  :
  C0 /5\ _is_even <*> _is_evenL <5= _is_evenL <*> _is_even
.
Proof.
  ii. unfold C0 in *. unfold compose in *. des. rename x0 into rr.
  (* revert PR. *)
  induction PR0; i; r in PR; des; clarify.
  - r. esplits; et. admit "??".
Abort.

Lemma decompat
  :
  C0 /5\ (_is_even /5\ id) <*> _is_evenL <5= _is_evenL <*> (_is_even /5\ id)
.
Proof.
  ii. unfold C0 in *. unfold id, compose in *. des. rename x0 into rr.
  (* revert PR. *)
  induction PR0; i; r in PR; des; clarify.
  - r. esplits; et. admit "??".
Abort.

Definition _is_evenL_e: (ord -> ord -> conat -> conat -> Prop) -> ord -> ord -> conat -> conat -> Prop :=
  ((∘) ∘ (∘)) (fun is_even n m => is_even (S (S n)) m)
.

Goal _is_evenL <*> _is_evenL_e <5= id.
Proof. i. unfold compose, id in *. r in PR. des; clarify. Qed.

Goal id <5= _is_evenL_e <*> _is_evenL.
Proof. i. unfold compose, id in *. rr. esplits; eauto. Qed.

Reset _is_evenL_e.

(* e1 x = /\ y. (x ≤ d y) *)
Definition _is_evenL_e: (ord -> ord -> conat -> conat -> Prop) -> ord -> ord -> conat -> conat -> Prop :=
  fun x => (∧_{ y ∈ { y | x <4= (_is_evenL y) } } (y $))
.
Definition _is_evenL_e2: (ord -> ord -> conat -> conat -> Prop) -> ord -> ord -> conat -> conat -> Prop :=
  (fun x _x0 _x1 _x2 _x3 => forall (y: (ord -> ord -> conat -> conat -> Prop)) (LE: x <4= _is_evenL y), y _x0 _x1 _x2 _x3)
.

Lemma is_evenL_e_mon: monotone4 _is_evenL_e2.
Proof. ii. r in IN. eapply IN; eauto. Qed.

Lemma is_evenL_e_unfold: _is_evenL_e = _is_evenL_e2.
Proof.
  extensionalities r x0 x1 x2 x3.
  eapply prop_ext. split; ii; r in H.
  - unshelve exploit H.
    { econs. eapply LE. }
    i. ss.
  - destruct _a. ss. eapply H; eauto.
Qed.

Goal id <5= _is_evenL <*> _is_evenL_e.
Proof. i. rewrite is_evenL_e_unfold. unfold compose, id in *. r. Abort.

Goal id <5= C1 <*> _is_evenL <*> _is_evenL_e <*> C0.
Proof.
  i. unfold compose, id in *. r.
  destruct (classic (_is_evenL_cond x1 x2 x3 x4)); et.
  right. r in H. des; clarify.
  r. esplits; et. rewrite is_evenL_e_unfold. r. i.
  exploit LE.
  { r. esplits; eauto. r. esplits; et. }
  intro T. r in T. des; clarify.
Qed.

Goal (_is_evenL_e <*> C0) <*> _is_even <5= _is_even <*> (_is_evenL_e <*> C0).
Proof.
  i. unfold compose in *. rewrite is_evenL_e_unfold in PR. r in PR.
  eapply PR. i. r in PR0. des. r in PR0. des; clarify.
  r. esplits; et.
  rewrite is_evenL_e_unfold.
  clear - PR1.
  dependent induction PR1.
  -
    
Abort.

Goal wrespectful4 _is_even (_is_evenL_e <*> C0).
Proof.
  econs; eauto.
  { admit "ez". }
  i. unfold compose in *. rewrite is_evenL_e_unfold in *. r in PR. eapply PR. i.
  r in PR0. des. r in PR0. des; clarify. r. esplits; et.
  dup PR1. eapply GF in PR0.
  inv PR0.
  { destruct (classic (ps0 = ps1)).
    - subst. eapply is_even_mon.
Qed.

Goal (_is_evenL_e <*> C0) <*> (_is_even /5\ id) <5= (_is_even /5\ id) <*> (_is_evenL_e <*> C0).
Proof.
  i. unfold compose in *. rewrite is_evenL_e_unfold in PR. r in PR.
  eapply PR. i. r in PR0. des. r in PR0. des; clarify.
  r. unfold id in *. esplits; et.
  - inv PR1.
  -
  i. unfold compose in *. rewrite is_evenL_e_unfold in PR. r in PR.
  esplits.
  - hexploit PR.
    { i. r in PR0. des. unfold id in *.
Abort.

(* Goal _is_evenL_e <*> _is_evenL <5= id. *)
(* Proof. i. unfold compose, id in *. rr. esplits; eauto. Qed. *)


From Ordinal Require Import Inaccessible Inaccessibility.
Module TMP.
Section TMP.
Universe i.
Set Printing Universes.
Axiom myty: nat -> Type@{i}.
Axiom intro_myty: forall n, myty n = unit.

Definition sig0: Type@{i} := { n: nat & myty n }.
Definition phi0: forall n, myty n. intros. rewrite intro_myty. apply tt. Qed.
Check sig0: Type@{i}.
Check forall n, myty n: Type@{i}.

Variable A: Type@{i}.
Variable B: (A -> Type@{i}).
Fail Check ((A -> Type@{i}): Type@{i}).
Fail Check (Type@{i}: Type@{i}).
Definition sig1: Type@{i} := { a: A & B a }.
Definition phi1: A -> Type@{i} := B.

Variable I: Type@{i} -> Prop.
Fail Let cup: Type@{i} := { T: Type@{i} | I T }.
Let cup: Type@{i+1} := { T: Type@{i} | I T }.
End TMP.
End TMP.

Lemma decompat
  :
  _is_even <*> (fun rec => _is_evenL_cond -4> _is_evenL rec) <5= (fun rec => _is_evenL_cond -4> _is_evenL rec) <*> _is_even
.
Proof.
  ii. rename x0 into rr. unfold compose in *.
  induction PR.
  - rr in PR0. des; clarify.
  - rr in PR0. des; clarify.
    rr. esplits; eauto.
    admit "idk yet".
Abort.

Lemma decompat
  :
  (_is_even /5\ id) <*> (fun rec => _is_evenL_cond -4> _is_evenL rec)
  <5= (fun rec => _is_evenL_cond -4> _is_evenL rec) <*> (_is_even /5\ id)
.
Proof.
  ii. rename x0 into rr. unfold compose in *. unfold id in *.
  induction PR.
  - rr in PR0. des; clarify. r. esplits; et.
    admit "idk yet".
Abort.

Lemma decompat_cond
  :
  (* _is_even <*> (_is_evenL) <5= (_is_evenL) <*> (* (fun rec => _is_evenL_cond -4> _is_even rec) *) _is_even *)
  ((fun _ => _is_evenL_cond) /5\ ((_is_even <*> _is_evenL)) <5= (_is_evenL <*> _is_even))
.
Proof.
  ii. rename x0 into rr. unfold compose in *. ii. des.

  {
    inv PR.
    inv PR0.
    - r. esplits; eauto. eapply is_even_mon; et. ii. admit "??".
    - r. esplits; eauto. econs; eauto. inv H.
      + eapply is_even_mon; et. ii. admit "??".
      + econs; eauto. inv H0.
        * eapply is_even_mon; et. admit "??".
        * econs; et. inv H.
Abort.
  (* induction PR0. *)
  (* - rr in PR. des; clarify. *)
  (* - rr in PR. des; clarify. *)
  (*   rr. esplits; eauto. *)
  (*   admit "idk yet". *)


(*
compat: uf <= fu
compat': u(f /\ 1) <= (f /\ 1)u

(uf <= fu) /\ (uf <= u) /\ (u <= fu)

respcetful: (l <= r /\ l <= f r) -> u l <= f u r

(l <= r /\ l <= fr) -> ul <= fur
----------------------------------
u(f /\ 1) <= (f /\ 1)u

put l <-| (f /\ 1). r <-| 1. we have
u(f /\ 1) <= f u.



u(f /\ 1) <= fu
u(f /\ 1)r <= fur
l <= r
l <= fr
----------------------------------
ul <= fur

ETS: ul <= u(f /\ 1)r
ETS: l <= fr /\ r
ez.

respcetful: (l <= r /\ l <= f r) -> u l <= f u+ r

*)
Lemma decompat_cond
  :
  (* _is_even <*> (_is_evenL) <5= (_is_evenL) <*> (* (fun rec => _is_evenL_cond -4> _is_even rec) *) _is_even *)
  ((fun _ => _is_evenL_cond) /5\ (((_is_even /5\ id) <*> _is_evenL)) <5= (_is_evenL <*> _is_even))
.
Proof.
  ii. rename x0 into rr. unfold compose in *. des. unfold id in *. r in PR. des; subst.
  induction PR0.
  { inv PR1. des; clarify. }
  { inv PR1. des; clarify.
    r. esplits; eauto. clear H0. clear IHPR0. induction PR0.
    - econs; eauto.
    - econs. eapply IHPR0.
    - econs; eauto.
    - r in H. des; subst. econs; eauto. admit "??".
  }
Abort.



Section MINKI.
  Definition _is_evenL_e (is_even: bool -> bool -> conat -> conat -> Prop) (f_src f_tgt: bool) (n m: conat): Prop :=
    is_even false f_tgt (S (S n)) m.

  Lemma WRES: wrespectful4 _is_even _is_evenL.
  Proof.
    econs; eauto.
    { admit "ez". }
    i. inv PR. des. subst.
    econs; eauto.
  Abort.

  Lemma WRES_e: wrespectful4 _is_even _is_evenL_e.
  Proof.
    econs; eauto.
    { admit "ez". }
    i. (* set (N:=x0). set(m:=x1). *)
    r in PR. dup PR. eapply GF in PR. eapply LE in PR0.
    remember (S (S x2)) as tmp. revert Heqtmp. revert x0 x2 PR0.
    induction PR; i; clarify.
    { eapply IHPR.
    { (* unprovable when x0 = 1 *)
      admit "??". }
  Abort.

  Goal _is_evenL_e <*> (cpn4 _is_even) <5= (cpn4 _is_even).
  Proof.
    ii. r in PR. eapply cpn4_cpn.
    { admit "ez". }
    eapply wrespect4_companion; eauto.
    { admit "ez". }
    { Abort.

End MINKI.

(* Lemma decompat *)
(*   : *)
(*   _is_even <*> is_evenL <3= is_evenL <*> _is_even *)
(* . *)
(* Proof. *)
(*   ii. unfold compose in *. *)
(*   rr in PR0. des. subst. *)
(*   rr. esplits; eauto. *)
(*   inv PR; ss. *)
(*   (* if n' is not even it does not hold *) *)
(* Abort. *)

(* (* maybe the theory needs to recognize conditions? *) *)

(* Lemma decompat *)
(*   : *)
(*   (_is_even \3/ id) <*> _is_evenL <3= _is_evenL <*> (_is_even \3/ id) *)
(* . *)
(* Abort. *)
(* (* it does not help *) *)

(* Lemma decompat *)
(*   : *)
(*   (* forall r n m (COND: _is_evenL_cond n m), ((_is_even <*> _is_evenL) r n m) <0= ((_is_evenL <*> _is_even) r n m) *) *)
(*   ((fun _ => _is_evenL_cond) /3\ ((_is_even <*> _is_evenL)) <3= (_is_evenL <*> _is_even)) *)
(* . *)
(* Proof. *)
(*   i. unfold compose in *. des. *)
(*   inv PR. *)
(*   rr. esplits; eauto. *)
(*   inv PR0; ss. *)
(*   - rr in H0. des. subst. econs; eauto. *)
(*   - rr in H. des. clarify. econs; eauto. *)
(* Qed. *)

Theorem is_evenL_simpl
  :
  paco4 _is_even bot4 <4= (fun rec => _is_evenL_cond -4> _is_evenL rec) (upaco4 _is_even bot4)
.
Proof.
  ii. punfold PR. r in PR0. induction PR.
  - des; clarify.
  - des; clarify. r. esplits; eauto.
  - des; clarify. r. esplits; eauto. exploit IHPR; eauto. intro T. r in T. des; clarify. pclearbot. left.
    admit "use left step closure".
  - r in H. des; clarify. r. esplits; eauto. left.
    punfold H. induction H.
    + pfold. econs; eauto. left.
    + ii. inv PR. clarify. econs; eauto.
  - r in H. des; ss.
    + ii. inv PR. r. esplits; eauto. left.
      { revert_until m. revert m. pcofix CIH.
        i. punfold H0. inv H0.
        - r in H1. des; ss.
          { pfold. econs; eauto. left. eapply paco2_mon; eauto. ii; ss. }
        - r in H. des; ss.
          { pfold. econs; eauto. }
      }
Qed.

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
Abort.
