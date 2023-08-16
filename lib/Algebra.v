Require Import Coqlib sflib.

(*** From stdpp ***)
Class Equiv (A: Type) := equiv: A -> A -> Prop.
Global Instance equiv_rewrite_relation `{Equiv A} :
  RewriteRelation (@equiv A _) | 150 := {}.
Notation "≡" := equiv (at level 70).
Infix "≡" := equiv (at level 70, no associativity).
Infix "≡@{ A }" := (@equiv A _)
  (at level 70, only parsing, no associativity).

Class OPlus (T: Type) := oplus: T -> T -> T.
Notation "(⊕)" := oplus (at level 50).
Notation "a ⊕ b" := (oplus a b) (at level 50, left associativity).

Class Bar (T: Type) := bar: T -> T.
Notation "|-|" := bar (at level 50).
Notation "| a |" := (bar a) (at level 50).

Class Ref (T: Type) := ref : T -> T -> Prop.

Definition ref_both `{Ref T}: T -> T -> Prop := fun a b => ref a b /\ ref b a.

Notation "⊑" := ref (at level 60).
Notation "a ⊑ b" := (ref a b) (at level 60, right associativity).
Notation "⊒⊑" := ref_both (at level 60).
Notation "a ⊒⊑ b" := (ref_both a b) (at level 60).

Global Program Instance ref_both_ref `{Ref T}: subrelation ((⊒⊑)) ((⊑)).
Next Obligation.
  rr in H0. des; eauto.
Qed.

Global Program Instance ref_both_ref2 `{Ref T}: subrelation ((⊒⊑)) (flip (⊑)).
Next Obligation.
  rr in H0. des; eauto.
Qed.

Global Program Instance equiv_ref_both `{Equiv T, Ref T, !Symmetric (≡), !subrelation (≡) (⊑)}: subrelation (≡) (⊒⊑).
Next Obligation.
  rr. esplits; et.
Qed.

Class Eps (T: Type) := eps : T.
Notation "'ε'" := eps.

Class EquivFacts `{Equiv T} := equiv_facts:> Equivalence ((≡)).

Class RefFacts `{Equiv T, Ref T, OPlus T} := {
    ref_Preorder:> PreOrder ((⊑));
    ref_oplus:> Proper ((⊑) ==> (⊑) ==> (⊑)) ((⊕));
    ref_equiv:> subrelation ((≡)) ((⊑));
}.

Global Program Instance ref_Proper `{Equiv T, Ref T, OPlus T, !RefFacts, !EquivFacts}: Proper ((≡) ==> (≡) ==> impl) ((⊑)).
Next Obligation.
  ii. etrans; et.
  { eapply ref_equiv; et. sym; et. }
  etrans; et.
  { eapply ref_equiv; et. }
Qed.

Global Program Instance ref_both_Equivalence `{Equiv T, Ref T, OPlus T} `{!EquivFacts} `{!RefFacts}: Equivalence ((⊒⊑)).
Next Obligation.
  ii. rr. esplits; try refl.
Qed.
Next Obligation.
  ii. rr. rr in H4. des. esplits; ss.
Qed.
Next Obligation.
  ii. rr. rr in H4. rr in H5. des. esplits; try etrans; et.
Qed.

Global Program Instance ref_both_OPlus `{Equiv T, Ref T, OPlus T} `{!EquivFacts} `{!RefFacts}:
  Proper ((⊒⊑) ==> (⊒⊑) ==> (⊒⊑)) ((⊕)).
Next Obligation.
  ii. rr. rr in H4. rr in H5. des. esplits; try apply ref_oplus; et.
Qed.

Global Program Instance ref_both_Proper `{Equiv T, Ref T, OPlus T} `{!EquivFacts} `{!RefFacts}:
  Proper ((≡) ==> (≡) ==> impl) ((⊒⊑)).
Next Obligation.
  ii. rr. rr in H6. des. rewrite H4 in *. rewrite H5 in *. esplits; et.
Qed.

Class BarFacts `{Equiv T, Bar T, OPlus T} := {
    bar_idemp: forall a, | |a| | ≡ |a|;
    bar_oplus: forall a b, |a ⊕ b| ≡ |a| ⊕ |b|;
    bar_Proper:> Proper ((≡) ==> (≡)) (|-|);
}.

Class BarFactsWeak `{Equiv T, Bar T, OPlus T, Ref T} := {
    bar_idemp_weak: forall a, | |a| | ⊒⊑ |a|;
    bar_oplus_weak: forall a b, |a ⊕ b| ⊒⊑ |a| ⊕ |b|;
    bar_Proper_weak:> Proper ((≡) ==> (≡)) (|-|);
}.

Global Program Instance BarFactsWeaken `{Equiv T, Bar T, OPlus T, Ref T, !EquivFacts, !BarFacts, !RefFacts}: BarFactsWeak.
Next Obligation. rewrite bar_idemp. refl. Qed.
Next Obligation. rewrite bar_oplus. refl. Qed.

(* Class OPlusFacts `{Equiv T, OPlus T, Ref T} `{EQVF: EquivFacts T} `{@RefFacts _ _ EQVF _ _} := { *)
Class OPlusFacts `{Equiv T, OPlus T} := {
    oplus_comm: forall (a b: T), a ⊕ b ≡ b ⊕ a;
    oplus_assoc: forall a b c, a ⊕ (b ⊕ c) ≡ (a ⊕ b) ⊕ c;
    oplus_Proper:> Proper ((≡) ==> (≡) ==> (≡)) ((⊕));
}.

Class OPlusFactsWeak `{Equiv T, OPlus T, Ref T} := {
    oplus_comm_weak: forall (a b: T), a ⊕ b ⊑ b ⊕ a;
    oplus_assoc_weak: forall a b c, a ⊕ (b ⊕ c) ⊑ (a ⊕ b) ⊕ c;
    oplus_Proper_weak:> Proper ((≡) ==> (≡) ==> (≡)) ((⊕));
}.

Global Program Instance OPlusFactsWeaken `{Equiv T, OPlus T, Ref T, !EquivFacts, !OPlusFacts, !RefFacts}: OPlusFactsWeak.
Next Obligation. rewrite oplus_comm. refl. Qed.
Next Obligation. rewrite oplus_assoc. refl. Qed.

Lemma oplus_assoc_weak2 `{Equiv T, OPlus T, Ref T, !OPlusFactsWeak, !PreOrder ((⊑))}: forall a b c, (a ⊕ b) ⊕ c ⊑ a ⊕ (b ⊕ c).
Proof.
  ii. rewrite oplus_comm_weak. rewrite oplus_assoc_weak. rewrite oplus_comm_weak. rewrite oplus_assoc_weak.
  rewrite oplus_comm_weak. refl.
Qed.

Class EpsFacts `{Equiv T, Eps T, OPlus T, Bar T} := {
    eps_r: forall a, a ⊕ ε ≡ a;
    eps_l: forall a, ε ⊕ a ≡ a;
    eps_bar: |ε| ≡ ε;
}.

Variant pointed (T: Type) :=
| just (t: T)
| mytt
.
Arguments mytt {_}.
Arguments just {_}.

(**
Two possible choices: (1) define T and then lift it, or (2) define pointed T at the first place.
(1)
Pros: "just" does not appar to the user (it can very well be hidden in the logic or we can just use coercion, though)
Cons: We want (⊑) to imply (⊑B), but with the usual definition of (⊑), it requires an additional step
(there is no proper ε because of the focus-left/right thing).
If we define (⊑) as usual, we don't have proper unit but we need unit-like thing ε' that satisfies "∀ a, a ⊒⊑ a ⊕ ε'"
in order to prove subrelation against (⊑B). <---- Not really, you may use |a| as ε'.
It is not that bad in the sense that "ε'" does not appear to the user.
We may able to define (⊑) as a conjuction of usual (⊑) and (⊑B). But that does not look very elegant.
(pratically though, it will work without any additional obligation I guess. "sim" implies both (⊑) and (⊑B).

!!! If we go this way, we cannot even state affinity. !!!

(2)
Pros: We don't have to care about the above business of ε'.
Cons: If we go this way, we should avoid using any form of lifting ("op T -> op (pointed T)")
because it will be disastrously confusing. This means, the definition/proof of instances may be slightly tedious
(4 LOC more for each).
**)

Global Instance Eps_pointed {T}: Eps (pointed T) := mytt.

Global Instance OPlus_pointed `{OPlus T}: OPlus (pointed T) :=
  fun x y =>
    match x, y with
    | just x, just y => just (x ⊕ y)
    | just _, mytt => x
    | mytt, just _ => y
    | _, _ => ε
    end
.

Global Instance Equiv_pointed `{Equiv T}: Equiv (pointed T) :=
  fun x y =>
    match x, y with
    | just x, just y => x ≡ y
    | mytt, mytt => True
    | _, _ => False
    end
.

Global Instance Ref_pointed `{Ref T}: Ref (pointed T) :=
  fun x y =>
    match x, y with
    | just x, just y => x ⊑ y
    | mytt, mytt => True
    | _, _ => False
    end
.

Global Instance Bar_pointed `{Bar T}: Bar (pointed T) :=
  fun x =>
    match x with
    | just x => just (|x|)
    | mytt => ε
    end
.

Ltac upt :=
  repeat match goal with
    | [H: context[@Algebra.equiv _ (@Equiv_pointed _ _)] |- _] => unfold Algebra.equiv, Equiv_pointed in H
    | [ |- context[@Algebra.equiv _ (@Equiv_pointed _ _)]] => unfold Algebra.equiv, Equiv_pointed
    | [H: context[@Algebra.ref _ (@Ref_pointed _ _)] |- _] => unfold Algebra.ref, Ref_pointed in H
    | [ |- context[@Algebra.ref _ (@Ref_pointed _ _)]] => unfold Algebra.ref, Ref_pointed
    | [H: context[@Algebra.bar _ (@Bar_pointed _ _)] |- _] => unfold Algebra.bar, Bar_pointed in H
    | [ |- context[@Algebra.bar _ (@Bar_pointed _ _)]] => unfold Algebra.bar, Bar_pointed
    | [H: context[@Algebra.eps _ (@Eps_pointed _ _)] |- _] => unfold Algebra.eps, Eps_pointed in H
    | [ |- context[@Algebra.eps _ (@Eps_pointed _ _)]] => unfold Algebra.eps, Eps_pointed
    | [H: context[@Algebra.oplus _ (@OPlus_pointed _ _)] |- _] => unfold Algebra.oplus, OPlus_pointed in H
    | [ |- context[@Algebra.oplus _ (@OPlus_pointed _ _)]] => unfold Algebra.oplus, OPlus_pointed
    end.

Module MRA.

  (* Module NU. *)

  (* Class t: Type := { *)
  (*   car:> Type; *)
  (*   equiv:> Equiv car; *)
  (*   oplus:> OPlus car; *)
  (*   ref:> Ref car; *)
  (*   bar:> Bar car; *)
  (*   (* facts:> mixin car; *) *)
  (*   equiv_facts:> EquivFacts (T:=car); *)
  (*   ref_facts:> RefFacts (T:=car); *)
  (*   oplus_facts:> OPlusFactsWeak (T:=car); *)
  (*   bar_facts:> BarFactsWeak (T:=car); *)
  (* }. *)

  (* End NU. *)

  Class t: Type := {
    car:> Type;
    equiv:> Equiv car;
    oplus:> OPlus car;
    ref:> Ref car;
    bar:> Bar car;
    eps:> Eps car;
    (* facts:> mixin car; *)
    equiv_facts:> EquivFacts (T:=car);
    ref_facts:> RefFacts (T:=car);
    oplus_facts:> OPlusFactsWeak (T:=car);
    bar_facts:> BarFactsWeak (T:=car);
    eps_facts:> EpsFacts (T:=car);
    affinity: forall a, a ⊑ ε;
    bar_intro: forall a, a ⊑ a ⊕ |a|;
  }.

  (* Global Program Instance unitize (mra: NU.t): t := { *)
  (*   car := pointed mra.(NU.car); *)
  (* } *)
  (* . *)
  (* Next Obligation. *)
  (*   econs; ss. *)
  (*   - ii. upt. des_ifs; try refl. *)
  (*   - ii. upt. des_ifs; ss. upt. sym; et. *)
  (*   - ii. upt. des_ifs; ss. etrans; et. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   econs; ss. *)
  (*   - econs. *)
  (*     + ii. upt. des_ifs; try refl. *)
  (*     + ii. upt. des_ifs; try etrans; et. *)
  (*   - ii. upt. des_ifs. eapply ref_oplus; et. *)
  (*   - ii. upt. des_ifs. rewrite <- H. refl. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   econs; ss. *)
  (*   - ii. upt. des_ifs; try refl. eapply oplus_comm_weak. *)
  (*   - ii. upt. des_ifs; try refl. eapply oplus_assoc_weak. *)
  (*   - ii. upt. des_ifs; try refl. rewrite H. rewrite H0. refl. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   econs; ss. *)
  (*   - ii. upt. des_ifs; try refl. r. upt. esplits; eapply bar_idemp_weak. *)
  (*   - ii. upt. des_ifs; try refl; r; upt; esplits; try refl; try eapply bar_oplus_weak. *)
  (*   - ii. upt. des_ifs; try refl. eapply bar_Proper_weak; ss. *)
  (* Qed. *)
  (* Next Obligation. *)
  (*   econs; ss. *)
  (*   - ii. upt. des_ifs; try refl. *)
  (*   - ii. upt. des_ifs; try refl. *)
  (* Qed. *)

End MRA.

(* Global Instance eq_Equiv {T}: Equiv T | 100 := eq. *)
(* Global Program Instance Eps_pointed_facts `{OPlus T}: EpsFacts (T:=pointed T). *)
(* Next Obligation. *)
(*   destruct a; ss. *)
(* Qed. *)
(* Next Obligation. *)
(*   destruct a; ss. *)
(* Qed. *)

Class RefB (T: Type) := refb: T -> T -> Prop.
Notation "⊑B" := refb (at level 50).
Notation "a ⊑B b" := (refb a b) (at level 50).

Class RefBFacts `{Equiv T, Ref T, RefB T} := {
    refb_Preorder:> PreOrder ((⊑B));
    ref_refb:> subrelation ((⊑)) ((⊑B));
    refb_equiv:> subrelation ((≡)) ((⊑B));
}.

Global Program Instance refB_Proper
  `{Equiv T, Ref T, RefB T, OPlus T, !RefBFacts, !EquivFacts}: Proper ((≡) ==> (≡) ==> impl) ((⊑B)).
Next Obligation.
  ii. etrans; et.
  { eapply refb_equiv; et. sym; et. }
  etrans; et.
  { eapply refb_equiv; et. }
Qed.
