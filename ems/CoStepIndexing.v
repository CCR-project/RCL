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


Fail Inductive myX: nat -> Type :=
| myX_recurse
    n
    (REC: myX n -> Type)
  :
  myX (n + 1)
.

(**
itree = ret r | tau itree | vis (X -> itree)
more interesting case would be lambda calculus
 **)

(* Inductive term: Type := *)
(* | Var : nat -> term *)
(* | App : term -> term -> term *)
(* | Lam : (term -> term) -> term *)
(* . *)

Module TEST.
Inductive test: Type :=
| test_intro
    (* (T: test -> Prop) <--- this is of size (2^test), so should be rejected *)
    Y (T: Y -> test) (* <--- this is of size Y^X, and it also should be rejected? *)
.
Set Printing Universes.
(* no, it is not rejected. but the universe constraint guarantees consistency. *)
Universe i.
Variable T: Type@{i}.
Check (forall (t: T), nat).
Check (forall (t: T), Prop).
Check (forall (n: nat), T).
Check (forall (p: Prop), T).
Record tmp: Type := mk { data: T }. Reset tmp.
Record tmp: Type := mk { data: forall (t: T), nat }. Reset tmp.
Record tmp: Type := mk { data: forall (t: T), Prop }. Reset tmp.
Record tmp: Type := mk { data: forall (p: Prop), T }. Reset tmp.
Check (forall (U: Type@{i}), U).
Check (forall (U: Type@{i}), Prop).
Check (Type@{i} -> nat).
Check (nat -> Type@{i}).
End TEST.



Variant myXF (myX: nat -> Type): nat -> Type :=
| myX_recurse
    n
    (REC: myX n -> Prop)
  :
  myXF myX (n + 1)
.

Definition myX: nat -> Type.
  fix IH 1.
  intro.
  destruct H.
  { exact unit. }
  { exact (@myXF IH H). }
Fail Defined.
Abort.

Fail Definition myX: nat -> Type :=
  fix go (n: nat): Type :=
    match n with
    | S m => (myXF go m)
    | _ => unit
    end
.

(* Fixpoint myX (k: nat): Type := *)
(*   match k with *)
(*   | 0 => unit *)
(*   | S k => myXF *)
(*   ... *)
(* Fixpoint A' (k : nat) : { C : ofe & Cofe C } := *)
(*   match k with *)
(*   | 0 => existT (P:=Cofe) unitO _ *)
(*   | S k => existT (P:=Cofe) (@oFunctor_apply F (projT1 (A' k)) (projT2 (A' k))) _ *)
(*   end. *)

(***
here, ofunctor is ofe -> ofe
ofe is just a type with step-indexed equality
so the type itself is not step-indexed
***)


(***
우리는 existential property 관심 없으니까 transfinite iris의 counter example에서는 벗어날 수 있을 수 있음
***)

(***
Definition oneShotΣ (F : oFunctor) : gFunctors :=
  #[ GFunctor (csumRF (exclRF unitO) (agreeRF (▶ F))) ].
***)





Variable X: Type.

Inductive iProp (iPropF: nat -> (X -> iProp) -> Prop): nat -> (X -> iProp) -> Prop :=
.

(** iProp := (X -> iProp) -> Prop **)

(**
progress flag -> conat
conat increases

progress: conat decreases by one to get coinductive hypothesis of 1

 **)
