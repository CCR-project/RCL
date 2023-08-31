Require Import Coqlib sflib String.
From stdpp Require Export base tactics.

Class OPlus (T: Type) := oplus: T -> T -> T.
Notation "(⊕)" := oplus (at level 50).
Notation "a ⊕ b" := (oplus a b) (at level 50, left associativity).

Class Bar (T: Type) := bar: T -> T.
Notation "|-|" := bar (at level 50).
Notation "| a |" := (bar a) (at level 50).

(* Notation "'ref'" := sqsubseteq (at level 60, only parsing). *)
Notation "'Ref'" := SqSubsetEq (at level 60, only parsing).
Definition ref_both `{Ref T}: T -> T -> Prop := λ a b, a ⊑ b /\ b ⊑ a.

(* Notation "⊒⊑" := ref_both (at level 70). *)
(* Notation "a ⊒⊑ b" := (ref_both a b) (at level 70). *)
Infix "⊒⊑" := ref_both (at level 70) : stdpp_scope.
Notation "(⊒⊑)" := ref_both (only parsing) : stdpp_scope.
Notation "( x ⊒⊑.)" := (ref_both x) (only parsing) : stdpp_scope.
Notation "(.⊒⊑ y )" := (λ x, ref_both x y) (only parsing) : stdpp_scope.

Infix "⊒⊑@{ A }" := (@ref_both A _) (at level 70, only parsing) : stdpp_scope.
Notation "(⊒⊑@{ A } )" := (@ref_both A _) (only parsing) : stdpp_scope.

Global Program Instance ref_both_ref `{Ref T}: subrelation ((⊒⊑)) ((⊑@{T})).
Next Obligation.
  i. rr in H0. des; eauto.
Qed.

Global Program Instance ref_both_ref2 `{Ref T}: subrelation ((⊒⊑)) (flip (⊑@{T})).
Next Obligation.
  i. rr in H0. des; eauto.
Qed.

Global Program Instance equiv_ref_both `{Equiv T, Ref T, !Symmetric (≡), !subrelation (≡) (⊑)}: subrelation (≡) (⊒⊑).
Next Obligation.
  i. rr. esplits; et.
Qed.

Class Eps (T: Type) := eps : T.
Notation "'ε'" := eps.

Class Wrap (S T: Type) := wrap: S -> T -> T.
Notation "'𝑤'" := (wrap) (at level 50).
Notation "𝑤_{ s }" := (wrap s) (at level 50).
Notation "𝑤_{ s } t" := (wrap s t) (at level 50).

Class EquivFacts `{Equiv T} := equiv_facts:> Equivalence ((≡)).

Class RefFacts `{Equiv T, Ref T, OPlus T} := {
    ref_Preorder:> PreOrder ((⊑@{T}));
    ref_oplus:> Proper ((⊑) ==> (⊑) ==> (⊑)) ((⊕));
    ref_equiv:> subrelation ((≡)) ((⊑));
}.

Global Program Instance ref_Proper `{Equiv T, Ref T, OPlus T, !RefFacts, !EquivFacts}: Proper ((≡) ==> (≡) ==> impl) ((⊑)).
Next Obligation.
  ii. etrans.
  { eapply ref_equiv. sym; et. }
  etrans; et.
  { eapply ref_equiv; et. }
Qed.

Global Program Instance ref_both_Equivalence `{Equiv T, Ref T, OPlus T} `{!EquivFacts} `{!RefFacts}: Equivalence ((⊒⊑@{T})).
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

Class BarFacts `{Equiv T, Bar T, OPlus T, Eps T} := {
    bar_idemp: forall a, | |a| | ≡ |a|;
    bar_oplus: forall a b, |a ⊕ b| ≡ |a| ⊕ |b|;
    bar_Proper:> Proper ((≡) ==> (≡)) (|-|);
    bar_eps: |ε| ≡ ε;
}.

Class BarFactsWeak `{Equiv T, Bar T, OPlus T, Ref T, Eps T} := {
    bar_idemp_weak: forall a, | |a| | ⊒⊑ |a|;
    bar_oplus_weak: forall a b, |a ⊕ b| ⊒⊑ |a| ⊕ |b|;
    bar_Proper_weak:> Proper ((≡) ==> (≡)) (|-|);
    bar_eps_weak: |ε| ≡ ε;
}.

Global Program Instance BarFactsWeaken `{Equiv T, Bar T, OPlus T, Ref T, Eps T, !EquivFacts, !BarFacts, !RefFacts}: BarFactsWeak.
Next Obligation. i. rewrite bar_idemp. refl. Qed.
Next Obligation. i. rewrite bar_oplus. refl. Qed.
Next Obligation. i. rewrite bar_eps. refl. Qed.

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
Next Obligation. i. rewrite oplus_comm. refl. Qed.
Next Obligation. i. rewrite oplus_assoc. refl. Qed.

Lemma oplus_assoc_weak2 `{Equiv T, OPlus T, Ref T, !OPlusFactsWeak, !PreOrder ((⊑@{T}))}: forall a b c, (a ⊕ b) ⊕ c ⊑ a ⊕ (b ⊕ c).
Proof.
  ii. rewrite oplus_comm_weak. rewrite oplus_assoc_weak. rewrite oplus_comm_weak. rewrite oplus_assoc_weak.
  rewrite oplus_comm_weak. refl.
Qed.

Class EpsFacts `{Equiv T, Eps T, OPlus T} := {
    eps_r: forall a, a ⊕ ε ≡ a;
    eps_l: forall a, ε ⊕ a ≡ a;
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
    | [H: context[@equiv _ (@Equiv_pointed _ _)] |- _] => unfold equiv, Equiv_pointed in H
    | [ |- context[@equiv _ (@Equiv_pointed _ _)]] => unfold equiv, Equiv_pointed
    | [H: context[@sqsubseteq _ (@Ref_pointed _ _)] |- _] => unfold sqsubseteq, Ref_pointed in H
    | [ |- context[@sqsubseteq _ (@Ref_pointed _ _)]] => unfold sqsubseteq, Ref_pointed
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
  ii. etrans.
  { eapply refb_equiv. sym; et. }
  etrans; et.
  { eapply refb_equiv; et. }
Qed.



Module MRAS.

  Class t: Type := {
    car:> Type;
    equiv:> Equiv car;
    oplus:> OPlus car;
    ref:> Ref car;
    bar:> Bar car;
    eps:> Eps car;
    equiv_facts:> EquivFacts (T:=car);
    ref_facts:> RefFacts (T:=car);
    oplus_facts:> OPlusFacts (T:=car);
    bar_facts:> BarFacts (T:=car);
    eps_facts:> EpsFacts (T:=car);
    affinity: forall a, a ⊑ ε;
    bar_intro: forall a, a ≡ a ⊕ |a|;
  }.

End MRAS.

Global Instance equiv_relaxed `{M: MRA.t}: Equiv _ | 100
  := fun a b => a ⊒⊑ b /\ |a| ⊒⊑ |b|.

Global Program Instance MRA_to_MRAS (M: MRA.t): MRAS.t := {
  car := MRA.car;
  equiv := equiv_relaxed;
}.
Next Obligation.
  econs.
  - ii; ss.
  - ii; ss. rr in H. des. rr. esplits; sym; et.
  - ii; ss. rr in H. rr in H0. des. rr. esplits; etrans; et.
Qed.
Next Obligation.
  econs; try typeclasses eauto.
  ii. rr in H. des; ss. eapply H.
Qed.
Next Obligation.
  econs; try typeclasses eauto.
  - ii. rr. esplits; et.
    + r. esplits; eapply oplus_comm_weak.
    + rewrite ! bar_oplus_weak. r. esplits; eapply oplus_comm_weak.
  - ii. rr. esplits; et.
    + r. esplits; try eapply oplus_assoc_weak; try eapply oplus_assoc_weak2.
    + rewrite ! bar_oplus_weak. r.
      esplits; try eapply oplus_assoc_weak; try eapply oplus_assoc_weak2.
  - ii. rr in H. rr in H0. des. rr. esplits; et.
    + rewrite H. rewrite H0. refl.
    + rewrite ! bar_oplus_weak.
      rewrite H1. rewrite H2. refl.
Qed.
Next Obligation.
  econs; try typeclasses eauto.
  - ii. rr. esplits; et.
    + rewrite bar_idemp_weak. refl.
    + rewrite bar_idemp_weak. refl.
  - ii. rr. esplits.
    + rewrite bar_oplus_weak. refl.
    + rewrite bar_idemp_weak. rewrite ! bar_oplus_weak.
      rewrite ! bar_idemp_weak.
      refl.
  - ii. rr in H. des. rr. esplits; et.
    + rewrite ! bar_idemp_weak. ss.
  - rr. esplits; try rewrite ! bar_eps_weak; refl.
Qed.
Next Obligation.
  econs; try typeclasses eauto.
  - ii. rr. esplits; et.
    + rewrite eps_r. refl.
    + rewrite bar_oplus_weak. rewrite bar_eps_weak. rewrite eps_r. refl.
  - ii. rr. esplits; et.
    + rewrite eps_l. refl.
    + rewrite bar_oplus_weak. rewrite bar_eps_weak. rewrite eps_l. refl.
Qed.
Next Obligation.
  i. eapply MRA.affinity.
Qed.
Next Obligation.
  i. rr. esplits; ss.
  - rr. esplits; ss.
    + eapply MRA.bar_intro.
    + rewrite <- (eps_r a) at 3. eapply ref_oplus; ss. eapply MRA.affinity.
  - rr. esplits; ss.
    + rewrite bar_oplus_weak. eapply MRA.bar_intro.
    + rewrite bar_oplus_weak.
      rewrite <- (eps_r (|a|)) at 3.
      eapply ref_oplus; ss. eapply MRA.affinity.
Qed.

Global Program Instance hat_Proper `{MRA.t}: Proper ((≡) ==> equiv_relaxed) (fun x => x).
Next Obligation.
  ii. rr. esplits.
  - rewrite H0. refl.
  - rewrite H0. refl.
Qed.

Definition included `{OPlus T, Equiv T}: T -> T -> Prop :=
  fun a b => exists ctx, (a ⊕ ctx) ≡ b.
Notation "(≼)" := (included) (at level 50).
Notation "x ≼ y" := (included x y) (at level 50).

Section INCLUDEDFACTS.

  Context `{M: MRAS.t}.

  Global Program Instance included_sub :
    subrelation ((≡)) ((≼)).
  Next Obligation.
    ii; ss. r. exists ε. rewrite eps_r. ss.
  Qed.

  Global Program Instance included_Proper: Proper ((≡) ==> (≡) ==> impl) ((≼)).
  Next Obligation.
    ii; ss. r in H1. r. des. setoid_subst. et.
  Qed.

  Global Program Instance included_PreOrder: PreOrder ((≼)).
  Next Obligation.
    ii. rr. esplits; et. rewrite eps_r. refl.
  Qed.
  Next Obligation.
    unfold included. ii. des. esplits; et. setoid_subst. rewrite oplus_assoc. f_equal.
  Qed.

  Global Program Instance oplus_included: Proper ((≼) ==> (≼) ==> (≼)) ((⊕)).
  Next Obligation.
    unfold included.
    ii. des. setoid_subst. esplits; et. rewrite <- ! oplus_assoc. f_equiv.
    instantiate (1:=ctx0 ⊕ ctx).
    rewrite ! oplus_assoc. f_equiv.
    rewrite oplus_comm. f_equiv.
  Qed.

  Lemma unit_included: ∀ x, ε ≼ x.
  Proof.
    ii. r. esplits. rewrite eps_l. refl.
  Qed.

  Lemma included_ref: forall a b, a ≼ b -> b ⊑ a.
  Proof.
    ii. rr in H. des; setoid_subst. erewrite <- (eps_r a) at 2. eapply ref_oplus; try refl. eapply MRAS.affinity.
  Qed.

  Global Program Instance ref_included: Proper ((≼) ==> (≼) --> impl) (⊑).
  Next Obligation.
    ii. etrans.
    { eapply included_ref; et. }
    etrans; et.
    r in H1.
    { eapply included_ref; et. }
  Qed.

  Lemma bar_mono: ∀ a b, a ≼ b -> |a| ≼ |b|.
  Proof.
    ii. rr in H. des; setoid_subst. rewrite bar_oplus. r; et.
  Qed.

  Global Program Instance bar_included: Proper ((≼) ==> (≼)) (|-|).
  Next Obligation.
    ii. eapply bar_mono; et.
  Qed.

  Global Program Instance oplus_ref: Proper ((⊑) ==> (⊑) ==> (⊑)) ((⊕)).
  Next Obligation.
    ii. eapply ref_oplus; et.
  Qed.

End INCLUDEDFACTS.




Ltac r_first rs :=
  match rs with
  | (?rs0 ⊕ ?rs1) =>
    let tmp0 := r_first rs0 in
    constr:(tmp0)
  | ?r => constr:(r)
  end
.

Ltac r_solve :=
  repeat rewrite oplus_assoc;
  repeat (try rewrite eps_r; try rewrite eps_l);
  match goal with
  | [|- ?lhs ≡ (_ ⊕ _) ] =>
    let a := r_first lhs in
    try rewrite <- (oplus_comm a);
    try rewrite <- ! oplus_assoc;
    try (f_equiv; r_solve)
  | _ => try reflexivity
  end
.

Module CM.

  Class t: Type := {
    car:> Type;
    equiv:> Equiv car;
    oplus:> OPlus car;
    eps:> Eps car;
    equiv_facts:> EquivFacts (T:=car);
    oplus_facts:> OPlusFacts (T:=car);
    eps_facts:> EpsFacts (T:=car);
  }.

End CM.
Coercion MRA.car: MRA.t >-> Sortclass.
Coercion MRAS.car: MRAS.t >-> Sortclass.
Coercion CM.car: CM.t >-> Sortclass.



Module WA.
Section FUNCTOR.
  Context {A: MRAS.t}.
  Context {S: CM.t}.

  Class t := {
      morph:> Wrap S A;
      morph_oplus: forall s a b, (𝑤_{s} a) ⊕ (𝑤_{s} b) ≡ (𝑤_{s} (a ⊕ b));
      morph_unit: ∀ a, 𝑤_{ε} a ≡ a;
      morph_unit2: ∀ a, 𝑤_{a} ε ≡ ε;
      morph_Proper1:> Proper ((eq) ==> (≡) ==> (≡)) (𝑤);
      morph_Proper2:> Proper ((≡) ==> (eq) ==> (≡)) (𝑤);
  }.

  Global Program Instance morph_Proper `{t}: Proper ((≡) ==> (eq) ==> (≡)) (𝑤).
  Next Obligation. ii. rewrite H0. rewrite H1. refl. Qed.

  Class Idem `{W: t} :=
    morph_idem: ∀ s0 s1 a, 𝑤_{s1} (𝑤_{s0} a) ≡ 𝑤_{s0 ⊕ s1} a.

  Section THEORIES.

    Context `{t}.

    Lemma morph_mono: forall s a b, a ≼ b -> 𝑤_{s} a ≼ 𝑤_{s} b.
    Proof.
      ii. rr in H0. des; setoid_subst. rr. esplits; et. rewrite morph_oplus; ss.
    Qed.

    Global Program Instance morph_included: Proper (eq ==> (≼) ==> (≼)) (𝑤).
    Next Obligation.
      ii. subst. eapply morph_mono; et.
    Qed.

  End THEORIES.

End FUNCTOR.
End WA.
