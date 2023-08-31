From iris.algebra Require Export cmra.
From iris.prelude Require Import options.
Require Import Coqlib.

Require Import String.
Set Implicit Arguments.
Open Scope string_scope.
Open Scope list_scope.


Class ValidOp (A : Type) `{Valid A, Op A}: Prop := valid_op : ∀ (x y: A), ✓ (x ⋅ y) → ✓ x.
Global Hint Mode ValidOp ! - - : typeclass_instances.

Section ra_total.
  Local Set Default Proof Using "Type*".
  Context {A} `{EQV: Equiv A, OP: Op A, VALID: Valid A}.
  Context `{EQUIVALENCE: Equivalence A (≡)}.
  Context `{op_proper : @Proper (A -> A -> A) ((≡) ==> (≡) ==> (≡)) (op)}.
  Context `{valid_proper : Proper _ ((≡) ==> impl) (@valid A _)}.

  Context `{valid_op_l : @ValidOp A valid (⋅)}.

  Implicit Types x y : A.


  Global Instance cmra_valid_proper : Proper ((≡) ==> iff) (@valid A _).
  Proof.
    intros x y Hxy.
    split=> ?.
    { rewrite -Hxy. eauto. }
    { rewrite Hxy. eauto. }
  Qed.





  Definition cmra_update (x y : A) := ∀ mz, ✓ (x ⋅ mz) → ✓ (y ⋅ mz).
  Infix "~~>" := cmra_update (at level 70).
  Global Instance: Params (@cmra_update) 1 := {}.
  Notation "(~~>)" := cmra_update (only parsing).

  Global Instance cmra_update_proper_ :
    ∀ x, Proper ((≡) ==> flip impl) (cmra_update x).
  Proof.
    ii. setoid_subst. eapply H0; ss.
  Qed.
  Global Instance cmra_update_proper :
    Proper ((≡) ==> (≡) ==> iff) (cmra_update).
  Proof.
    rewrite /cmra_update=> x x' Hx y y' Hy; split=> ? mz ?; setoid_subst; auto.
  Qed.

  Definition cmra_update_both (x y : A) := x ~~> y ∧ y ~~> x.
  Infix "<~~>" := cmra_update_both (at level 70).
  Global Instance: Params (@cmra_update_both) 1 := {}.
  Notation "(<~~>)" := cmra_update_both (only parsing).

  Global Instance cmra_update_both_proper :
    Proper ((≡) ==> (≡) ==> iff) (cmra_update_both).
  Proof.
    rewrite /cmra_update=> x x' Hx y y' Hy. split=> T; r in T; r; des; split; setoid_subst; ss.
  Qed.
  Global Instance cmra_update_both_proper_ :
    ∀ x, Proper ((≡) ==> flip impl) (cmra_update_both x).
  Proof.
    ii. r in H0. r. des. setoid_subst. split; ss.
  Qed.

  Global Instance cmra_update_rewrite_relation :
    RewriteRelation (cmra_update) | 170 := {}.
  Global Instance cmra_update_preorder : PreOrder (cmra_update).
  Proof.
    econs.
    - ii; ss.
    - ii. eapply H0; et.
  Qed.

  Global Instance cmra_update_proper_update :
    Proper (flip cmra_update ==> cmra_update ==> impl) (cmra_update).
  Proof.
    intros x1 x2 Hx y1 y2 Hy ?. etrans; [apply Hx|]. by etrans; [|apply Hy].
  Qed.
  Global Instance cmra_update_flip_proper_update :
    Proper (cmra_update ==> flip cmra_update ==> flip impl) (cmra_update).
  Proof.
    intros x1 x2 Hx y1 y2 Hy ?. etrans; [apply Hx|]. by etrans; [|apply Hy].
  Qed.

  Global Instance cmra_update_both_rewrite_relation :
    RewriteRelation (cmra_update_both) | 170 := {}.
  Global Instance cmra_update_both_preorder : PreOrder (cmra_update_both).
  Proof.
    econs; ss.
    - split; ii; ss.
    - ii; ss. r in H; r in H0; des. split; etrans; et.
  Qed.
  Global Instance cmra_update_both_symm : Symmetric (cmra_update_both).
  Proof.
    ii. r in H; r; des. et.
  Qed.

  Global Instance cmra_update_both_equiv_subrel : subrelation (≡) (cmra_update_both).
  Proof. ii. rewrite H. ss. refl. Qed.
  Global Instance cmra_update_both_fpu_subrel : subrelation (<~~>) (~~>).
  Proof. ii. eapply H; et. Qed.
  Global Instance cmra_update_both_proper_update :
    Proper (flip cmra_update_both ==> cmra_update_both ==> impl) (cmra_update_both).
  Proof.
    intros x1 x2 Hx y1 y2 Hy ?. etrans; [apply Hx|]. by etrans; [|apply Hy].
  Qed.
  Global Instance cmra_update_both_flip_proper_update :
    Proper (cmra_update_both ==> flip cmra_update_both ==> flip impl) (cmra_update_both).
  Proof.
    intros x1 x2 Hx y1 y2 Hy ?. etrans; [apply Hx|]. by etrans; [|apply Hy].
  Qed.






  (* Context `{op_assoc : Assoc _ (≡) (@op A _)}. *)
  (* Context `{op_comm : Comm _ _ (≡) (@op A _)}. *)
  Context `{op_assoc : Assoc _ (<~~>) (@op A _)}.
  Context `{op_comm : Comm _ _ (<~~>) (@op A _)}.
  Context `{UNIT: Unit A}.
  Context `{unit_idl: LeftId _ (≡) (ε: A) (⋅)}.
  Context `{unit_idr: RightId _ (≡) (ε: A) (⋅)}.

  Global Program Instance fpu_fpub_proper: Proper ((<~~>) ==> (<~~>) ==> impl) (~~>).
  Next Obligation.
    ii. eapply H0. eapply H1. eapply H. et.
  Qed.
  Global Program Instance fpu_fpub_proper_: Proper ((<~~>) ==> (<~~>) ==> flip impl) (~~>).
  Next Obligation.
    ii. eapply H0. eapply H1. eapply H. et.
  Qed.
  Global Program Instance fpu_fpub_proper__: ∀ x, Proper ((<~~>) ==> flip impl) (cmra_update x).
  Next Obligation.
    i. eapply fpu_fpub_proper_. refl.
  Qed.

  Global Program Instance valid_fpu_proper: Proper ((~~>) ==> impl) (valid).
  Next Obligation.
    ii. specialize (H ε). rewrite <- unit_idr. eapply H. rewrite unit_idr. ss.
  Qed.

  Lemma cmra_update_op x1 x2 y1 y2 : x1 ~~> y1 → x2 ~~> y2 → x1 ⋅ x2 ~~> y1 ⋅ y2.
  Proof.
    unfold cmra_update. intros T U. intros fr V.
    rewrite -op_assoc in V. eapply T in V. rewrite op_comm in V. rewrite -op_assoc in V. eapply U in V.
    rewrite op_assoc in V. rewrite -op_comm in V. rewrite op_assoc in V. congruence.
    (* rewrite !cmra_update_updateP; eauto using cmra_updateP_op with congruence. *)
  Qed.

  Global Instance cmra_update_op_proper :
    Proper (cmra_update ==> cmra_update ==> cmra_update) (op (A:=A)).
  Proof. intros x1 x2 Hx y1 y2 Hy. by apply cmra_update_op. Qed.
  Global Instance cmra_update_op_flip_proper :
    Proper (flip cmra_update ==> flip cmra_update ==> flip cmra_update) (op (A:=A)).
  Proof. intros x1 x2 Hx y1 y2 Hy. by apply cmra_update_op. Qed.

  Lemma cmra_update_op_l x y : x ⋅ y ~~> x.
  Proof.
    ii. eapply valid_op_l; et. eapply valid_fpu_proper; try apply H.
    rewrite -assoc. rewrite -assoc. tactics.f_equiv. rewrite comm. refl. Qed.
  (* Proof. intros n mz. rewrite comm. rewrite comm cmra_op_opM_assoc. apply cmra_validN_op_r. Qed. *)
  Lemma cmra_update_op_r x y : x ⋅ y ~~> y.
  Proof. rewrite comm. apply cmra_update_op_l. Qed.

  Lemma cmra_update_included x y : x ≼ y → y ~~> x.
  Proof. intros [z ->]. apply cmra_update_op_l. Qed.




  Lemma cmra_update_both_op x1 x2 y1 y2 : x1 <~~> y1 → x2 <~~> y2 → x1 ⋅ x2 <~~> y1 ⋅ y2.
  Proof.
    unfold cmra_update_both. i. des.
    esplits; et.
    { rewrite H. rewrite H0. ss. }
    { rewrite H1. rewrite H2. ss. }
  Qed.

  Global Instance cmra_update_both_op_proper :
    Proper (cmra_update_both ==> cmra_update_both ==> cmra_update_both) (op (A:=A)).
  Proof. intros x1 x2 Hx y1 y2 Hy. by apply cmra_update_both_op. Qed.
  Global Instance cmra_update_both_op_proper_ :
    Proper (cmra_update_both ==> cmra_update_both ==> flip cmra_update_both) (op (A:=A)).
  Proof. intros x1 x2 Hx y1 y2 Hy. apply cmra_update_both_op; sym; et. Qed.
  Global Instance cmra_update_both_op_flip_proper :
    Proper (flip cmra_update_both ==> flip cmra_update_both ==> flip cmra_update_both) (op (A:=A)).
  Proof. intros x1 x2 Hx y1 y2 Hy. by apply cmra_update_both_op. Qed.

End ra_total.
Infix "~~>" := cmra_update (at level 70).
Notation "(~~>)" := cmra_update (only parsing).
Global Instance: Params (@cmra_update) 1 := {}.
Infix "<~~>" := cmra_update_both (at level 70).
Notation "(<~~>)" := cmra_update_both (only parsing).













Section SYNTAX.
  Context `{Equiv A} `{Op A} `{Valid A} `{PCore A} `{Unit A}.
  Inductive ResourceTree: Type :=
  | rt_leaf (a: A)
  | rt_core (rt: ResourceTree)
  | rt_op (rt0 rt1: ResourceTree)
  .
  Inductive FormulaTree: Type :=
  | ft_univ {X: Type} (ft: X -> FormulaTree)
  | ft_impl (ft0 ft1: FormulaTree)
  | ft_equiv (rt0 rt1: ResourceTree)
  | ft_valid (rt0: ResourceTree)
  | ft_fpu (rt0 rt1: ResourceTree)
  | ft_fpub (rt0 rt1: ResourceTree)
  | ft_incl (rt0 rt1: ResourceTree)
  | ft_assoc0
  | ft_assoc1
  | ft_comm0
  | ft_comm1
  .

  Fixpoint denote_rt (rt: ResourceTree): A :=
    match rt with
    | rt_leaf a => a
    | rt_core rt => core (denote_rt rt)
    | rt_op rt0 rt1 => (denote_rt rt0) ⋅ (denote_rt rt1)
    end
  .

  Fixpoint denote_ft (ft: FormulaTree): Prop :=
    match ft with
    | ft_univ ft => forall x, denote_ft (ft x)
    | ft_impl ft0 ft1 => denote_ft ft0 -> denote_ft ft1
    | ft_equiv rt0 rt1 => (denote_rt rt0) ≡ (denote_rt rt1)
    | ft_valid rt => ✓ (denote_rt rt)
    | ft_fpu rt0 rt1 => (denote_rt rt0) ~~> (denote_rt rt1)
    | ft_fpub rt0 rt1 => (denote_rt rt0) <~~> (denote_rt rt1)
    | ft_incl rt0 rt1 => (denote_rt rt0) ≼ (denote_rt rt1)
    | ft_assoc0 => @Assoc A (≡) (⋅)
    | ft_assoc1 => @Assoc A (~~>) (⋅)
    | ft_comm0 => @Comm A _ (≡) (⋅)
    | ft_comm1 => @Comm A _ (~~>) (⋅)
    end
  .
End SYNTAX.

Arguments FormulaTree: clear implicits.



Section RAAXIOMS.

  Class RAAxioms := {
    ra_axioms: ∀ A, list (FormulaTree A)
  }
  .

  (* { ra_op_proper : ∀ x : A0, Proper (base.equiv ==> base.equiv) (op x); *)
  (*   ra_validN_proper : Proper (base.equiv ==> impl) valid; *)
  (*   ra_assoc : Assoc base.equiv op; *)
  (*   ra_comm : Comm base.equiv op; *)
  (*   ra_valid_op_l : ∀ x y : A0, ✓ (x ⋅ y) → ✓ x }. *)

  (*   ra_core_proper : ∀ x y cx : A0, x ≡ y → pcore x = Some cx → ∃ cy : A0, pcore y = Some cy ∧ cx ≡ cy; *)
  (*   ra_pcore_l : ∀ x cx : A0, pcore x = Some cx → cx ⋅ x ≡ x; *)
  (*   ra_pcore_idemp : ∀ x cx : A0, pcore x = Some cx → pcore cx ≡ Some cx; *)
  (*   ra_pcore_mono : ∀ x y cx : A0, x ≼ y → pcore x = Some cx → ∃ cy : A0, pcore y = Some cy ∧ cx ≼ cy; *)

  (* Definition ft_valid_op_l: ∀ A, FormulaTree A := *)
  (*   λ A, ft_univ (λ '(x, y), ft_impl (ft_valid (rt_op (rt_leaf x) (rt_leaf y))) *)
  (*                                    (ft_valid (rt_leaf x))). *)
  Definition ft_core_proper: ∀ A, FormulaTree A :=
    λ A, ft_univ (λ '(x, y), ft_impl (ft_equiv (rt_leaf x) (rt_leaf y))
                               (ft_equiv (rt_core (rt_leaf x)) (rt_core (rt_leaf y)))).
  Definition ft_pcore_l: ∀ A, FormulaTree A :=
    λ A, ft_univ (λ x, ft_equiv (rt_leaf x) (rt_op (rt_leaf x) (rt_core (rt_leaf x)))).
  Compute denote_ft (ft_pcore_l nat).
  Definition ft_pcore_idemp: ∀ A, FormulaTree A :=
    λ A, ft_univ (λ x, ft_equiv (rt_core (rt_leaf x)) (rt_core (rt_core (rt_leaf x)))).
  Definition ft_pcore_mono: ∀ A, FormulaTree A :=
    λ A, ft_univ (λ '(x, y), ft_impl (ft_incl (rt_leaf x) (rt_leaf y))
                               (ft_incl (rt_core (rt_leaf x)) (rt_core (rt_leaf y)))).
  Definition ft_pcore_commut: ∀ A, FormulaTree A :=
    λ A, ft_univ (λ '(x, y), ft_equiv (rt_core (rt_op (rt_leaf x) (rt_leaf y)))
                               (rt_op (rt_core (rt_leaf x)) (rt_core (rt_leaf y)))).

  Instance RAX0: RAAxioms :=
    { ra_axioms := λ A, [ft_core_proper A; ft_pcore_l A; ft_pcore_idemp A; ft_pcore_mono A; ft_assoc0; ft_comm0] }.

  Instance RAX0plus: RAAxioms :=
    { ra_axioms := λ A, [ft_core_proper A; ft_pcore_l A; ft_pcore_idemp A; ft_pcore_commut A; ft_assoc0; ft_comm0 ] }.


(*
x ~~> x ⋅ |x|
||x|| <~~> |x|
|x ⋅ y| <~~> |x| ⋅ |y|
*)
  Definition ft_pcore_l1: ∀ A, FormulaTree A :=
    λ A, ft_univ (λ x, ft_fpu (rt_leaf x) (rt_op (rt_leaf x) (rt_core (rt_leaf x)))).
  Definition ft_pcore_idemp1: ∀ A, FormulaTree A :=
    λ A, ft_univ (λ x, ft_fpub (rt_core (rt_leaf x)) (rt_core (rt_core (rt_leaf x)))).
  Definition ft_pcore_commut1: ∀ A, FormulaTree A :=
    λ A, ft_univ (λ '(x, y), ft_fpub (rt_core (rt_op (rt_leaf x) (rt_leaf y)))
                                     (rt_op (rt_core (rt_leaf x)) (rt_core (rt_leaf y)))).
  Definition ft_pcore_proper1: ∀ A, FormulaTree A :=
    λ A, ft_univ (λ '(x, y), ft_impl (ft_equiv (rt_leaf x) (rt_leaf y))
                                     (ft_fpub (rt_core (rt_leaf x)) (rt_core (rt_leaf y)))).

  Instance RAX1: RAAxioms :=
    { ra_axioms := λ A, [ft_pcore_l1 A; ft_pcore_idemp1 A; ft_pcore_commut1 A; ft_pcore_proper1 A; ft_assoc1; ft_comm1] }.

(*
x ~~> x ⋅ |x|
||x|| <~~> |x|
*)

  Instance RAX2: RAAxioms :=
    { ra_axioms := λ A, [ft_pcore_l1 A; ft_pcore_idemp1 A] }.

  Context `{Equiv A} `{Op A} `{Valid A} `{PCore A} `{Unit A}.
  (* Definition ra_axioms_sat (RA: RAAxioms): Prop := ∀ ra (IN: ra ∈ (ra_axioms A)), denote_ft ra. *)
  Definition ra_axioms_sat (RA: RAAxioms): Prop := Forall (λ ra, denote_ft ra) (ra_axioms A).

  Definition RAX0_spec: ra_axioms_sat RAX0 <-> (
     (∀ x y : A, x ≡ y → core x ≡ core y) ∧
     (∀ x : A, x ≡ x ⋅ core x) ∧
     (∀ x : A, core x ≡ core (core x)) ∧
     (∀ x y : A, x ≼ y → core x ≼ core y) ∧
       @Assoc A (≡) (⋅) ∧ @Comm A _ (≡) (⋅)).
  Proof.
    unfold ra_axioms_sat. ss. ss; split; i.
    - repeat match goal with | [H: Forall _ _ |- _] => inv H end; ss.
      esplits; ss.
      + i. specialize (H7 (x, y)). ss. eauto.
      + i. specialize (H9 (x, y)). ss. eauto.
    - des. repeat econs; ss.
      + i. des_ifs. ss. eauto.
      + i. des_ifs. ss. eauto.
  Qed.

  Definition RAX0plus_spec: ra_axioms_sat RAX0plus <-> (
     (∀ x y : A, x ≡ y → core x ≡ core y) ∧
     (∀ x : A, x ≡ x ⋅ core x) ∧
     (∀ x : A, core x ≡ core (core x)) ∧
     (∀ x y : A, core (x ⋅ y) ≡ core x ⋅ core y) ∧
       @Assoc A (≡) (⋅) ∧ @Comm A _ (≡) (⋅)).
  Proof.
    unfold ra_axioms_sat. ss. ss; split; i.
    - repeat match goal with | [H: Forall _ _ |- _] => inv H end; ss.
      esplits; ss.
      + i. specialize (H7 (x, y)). ss. eauto.
      + i. specialize (H9 (x, y)). ss.
    - des. repeat econs; ss.
      + i. des_ifs. ss. eauto.
      + i. des_ifs. ss.
  Qed.

  Definition RAX1_spec: ra_axioms_sat RAX1 <-> (
     (∀ x : A, x ~~> x ⋅ core x) ∧
     (∀ x : A, (core x) <~~> core (core x)) ∧
     (∀ x y : A, core (x ⋅ y) <~~> core x ⋅ core y) ∧
     (∀ x y : A, x ≡ y -> core x <~~> core y) ∧
       @Assoc A (~~>) (⋅) ∧ @Comm A _ (~~>) (⋅)).
  Proof.
    unfold ra_axioms_sat. ss. ss; split; i.
    - repeat match goal with | [H: Forall _ _ |- _] => inv H end; ss.
      esplits; ss.
      + i. specialize (H8 (x, y)). ss.
      + i. specialize (H9 (x, y)). ss. eauto.
    - des. repeat econs; ss.
      + eapply H5.
      + eapply H5.
      + i. des_ifs. ss.
      + i. des_ifs. ss. eauto.
  Qed.

  Definition RAX2_spec: ra_axioms_sat RAX2 <-> (
     (∀ x : A, x ~~> x ⋅ core x) ∧
     (∀ x : A, (core x) <~~> core (core x))).
  Proof.
    unfold ra_axioms_sat. ss. ss; split; i.
    - repeat match goal with | [H: Forall _ _ |- _] => inv H end; ss.
    - des. repeat econs; ss.
      + eapply H5.
      + eapply H5.
  Qed.

  (* Record common_axioms: Prop := { *)
  (*   ca_Equivalence:> Equivalence (A:=A) equiv; *)
  (*   ca_op_proper:> ∀ (x: A), Proper (equiv ==> equiv) (op x); *)
  (*   ca_validN_proper:> Proper (equiv ==> impl) (valid (A:=A)); *)
  (*   ca_assoc:> Assoc (A:=A) (≡) (⋅); *)
  (*   ca_comm:> Comm (A:=A) (≡) (⋅); *)
  (*   ca_valid_op_l:> ∀ (x y: A), ✓ (x ⋅ y) → ✓ x; *)
  (* }. *)
  Definition common_axioms: Prop :=
    Equivalence (A:=A) equiv ∧ (* (∀ (x: A), Proper (equiv ==> equiv) (op x)) ∧ *)
      (@Proper (A -> A -> A) (equiv ==> equiv ==> equiv) (op)) ∧
      Proper (equiv ==> impl) (valid (A:=A)) (* ∧ Assoc (A:=A) (≡) (⋅) ∧ Comm (A:=A) (≡) (⋅) *)
    ∧ @ValidOp A valid (⋅) ∧ ✓ (ε: A) ∧ LeftId (≡) (ε: A) (⋅) ∧ RightId (≡) (ε: A) (⋅) ∧ core (ε: A) ≡ ε
  .

End RAAXIOMS.



Section REPLAY.

  Reserved Notation "a ^" (at level 20).
  Reserved Notation "a ^^" (at level 20).

  Class Replayable (RA0 RA1: RAAxioms) := {
    rp_Hat: ∀ (A: Type), Type where "A ^^" := (rp_Hat A);
    rp_hat: ∀ A, A -> rp_Hat A where "a ^" := (rp_hat a);

    rp_equiv:> ∀ `{Equiv A, Op A, Valid A, PCore A, Unit A}, Equiv (A ^^);
    rp_op:> ∀ `{Equiv A, Op A, Valid A, PCore A, Unit A}, Op (A ^^);
    rp_valid:> ∀ `{Equiv A, Op A, Valid A, PCore A, Unit A}, Valid (A ^^);
    rp_pcore:> ∀ `{Equiv A, Op A, Valid A, PCore A, Unit A}, PCore (A ^^);
    rp_unit:> ∀ `{Equiv A, Op A, Valid A, PCore A, Unit A}, Unit (A ^^);

    (* Equivalence should be part of "common axioms", but put out here for setoid rewrites. *)
    rp_sat: ∀ {A} {EQ: Equiv A} {OP: Op A} {VL: Valid A} {CR: PCore A} {UN: Unit A},
        (@ra_axioms_sat A _ _ _ _ RA0 ∧ common_axioms (A:=A)) ->
        @ra_axioms_sat (A ^^) _ _ _ _ RA1 ∧ common_axioms (A:=A^^);

    rp_hat_Proper: ∀ `{Equiv A, Op A, Valid A, PCore A, Unit A},
        ∀ (SAT: @ra_axioms_sat A _ _ _ _ RA0 ∧ common_axioms (A:=A)),
        Proper ((≡) ==> (≡)) (@rp_hat A);
    (*** below are trivial if rp_hat is an identity function and rp_hat_Proper (above) holds ***)
    rp_commut_op: ∀ {A} {EQ: Equiv A} {OP: Op A} {VL: Valid A} {CR: PCore A} {UN: Unit A},
        ∀ (SAT: @ra_axioms_sat A _ _ _ _ RA0 ∧ common_axioms (A:=A)),
        ∀ (x y: A), (x^ ⋅ y^) ≡ (x ⋅ y)^;
    rp_commut_core: ∀ {A} {EQ: Equiv A} {OP: Op A} {VL: Valid A} {CR: PCore A} {UN: Unit A},
        ∀ (SAT: @ra_axioms_sat A _ _ _ _ RA0 ∧ common_axioms (A:=A)),
        ∀ (x: A), (core x^) ≡ (core x)^;
    rp_commut_valid: ∀ {A} {EQ: Equiv A} {OP: Op A} {VL: Valid A} {CR: PCore A} {UN: Unit A},
        ∀ (SAT: @ra_axioms_sat A _ _ _ _ RA0 ∧ common_axioms (A:=A)),
        ∀ (x: A), ✓ (x^) <-> ✓ x;
    rp_commut_fpu: ∀ {A} {EQ: Equiv A} {OP: Op A} {VL: Valid A} {CR: PCore A} {UN: Unit A},
        ∀ (SAT: @ra_axioms_sat A _ _ _ _ RA0 ∧ common_axioms (A:=A)),
        ∀ (x y: A), (x ~~> y) <-> (x^ ~~> y^);
  }
  .
  Notation "a ^" := (rp_hat a).
  Notation "A ^^" := (rp_Hat A).

  Global Program Instance replayable_trans (RA0 RA1 RA2: RAAxioms)
                 (RPA: Replayable RA0 RA1) (RPB: Replayable RA1 RA2): Replayable RA0 RA2 := {
    rp_Hat := λ A, RPB.(rp_Hat) (RPA.(rp_Hat) A);
    rp_hat := λ A a, a^ ^;
    (* rp_hat := λ A a, RPB.(rp_hat) (RPA.(rp_hat) a); *)
  }.
  Next Obligation.
    ii. ss. exploit RPA.(rp_sat); eauto. { et. } intro T. exploit RPB.(rp_sat); eauto.
  Qed.
  Next Obligation.
    ii. ss. exploit RPA.(rp_sat); eauto. { et. } intro T. exploit RPB.(rp_sat); eauto. intro U. des.
    eapply rp_hat_Proper; eauto.
    eapply rp_hat_Proper; eauto.
  Qed.
  Next Obligation.
    ii. ss. exploit RPA.(rp_sat); eauto. { et. } intro T. exploit RPB.(rp_sat); eauto. intro U. des. destruct U0. destruct T0.
    erewrite rp_commut_op; ss; eauto.
    eapply rp_hat_Proper; ss; et.
    erewrite rp_commut_op; eauto.
  Qed.
  Next Obligation.
    ii. ss. exploit RPA.(rp_sat); eauto. { et. } intro T. exploit RPB.(rp_sat); eauto. intro U. des. destruct U0. destruct T0.
    ss.
  Qed.
  Next Obligation.
    ii. ss. exploit RPA.(rp_sat); eauto. { et. } intro T. exploit RPB.(rp_sat); eauto. intro U.
    rewrite rp_commut_valid; ss; eauto.
    rewrite rp_commut_valid; ss; eauto.
  Qed.
  Next Obligation.
    ii. ss. exploit RPA.(rp_sat); eauto. { et. } intro T. exploit RPB.(rp_sat); eauto. intro U.
    rewrite <- rp_commut_fpu; ss; eauto.
    rewrite <- rp_commut_fpu; eauto.
  Qed.

  Global Program Instance replayable_refl (RA: RAAxioms): Replayable RA RA := {
    rp_Hat := λ A, A;
    rp_hat := λ A a, a;
  }.
  Next Obligation. inv H0. refl. Qed.
  Next Obligation. inv H0. refl. Qed.

End REPLAY.
Notation "a ^" := (rp_hat a) (at level 20).
Notation "A ^^" := (rp_Hat A) (at level 20).



Ltac split_l :=
  try rewrite <- ! and_assoc;
  match goal with
  | [ |- ?A ∧ ?B ] =>
      let name := fresh "U" in cut A; [intro name; split; [exact name|]|]; cycle 1
  end.

Ltac split_r :=
  match goal with
  | [ |- ?A ∧ ?B ] =>
      let name := fresh "U" in cut B; [intro name; split; [|exact name]|]; cycle 1
  end.



Section RPL.
  Local Obligation Tactic := idtac.

  Global Program Instance replayable0: Replayable RAX1 RAX0plus := {
    rp_Hat := λ A, A;
    rp_hat := λ A a, a;
    rp_equiv := λ `{Equiv A, Op A, Valid A, PCore A, Unit A}, λ x y, x <~~> y ∧ core x <~~> core y;
  }.
  Next Obligation.
    ii. des. rename H0 into C; r in C; des.
    eapply RAX1_spec in H. rename H into T. des; ss.
    assert(tmp: Assoc cmra_update_both (@op A _)).
    { ii. split; et. rewrite T4. rewrite T3. rewrite T4. rewrite T3. rewrite T4. refl. }
    clear T3. rename tmp into T3.
    assert(tmp: Comm cmra_update_both (@op A _)).
    { ii. split; et. }
    clear T4. rename tmp into T4.
    split_l.
    - eapply RAX0plus_spec.
      assert(V0: ∀ (x :A), x <~~> x ⋅ core x).
      { i. split; i; ss. unshelve eapply cmra_update_included; et. r. et. }
      assert(V1: ∀ (x :A), core x <~~> core x ⋅ core x).
      { i. specialize (V0 (core x)). etrans; et. eapply cmra_update_both_op; et. sym; et. }
      split_l.
      { i. r in H. des. red. esplits; ss. rewrite <- T0. sym. rewrite <- T0. sym; et. }
      split_l.
      { i. r. esplits; ss. sym. rewrite T1. sym. etrans; try apply V1.
        eapply cmra_update_both_op_proper; et. }
      split_l.
      { ii. rr. esplits; ss. }
      split_l.
      { ii. r. esplits; et. rewrite <- ! T0. rewrite T1. sym. rewrite T1. sym.
        eapply cmra_update_both_op_proper; et. }
      split_l.
      { ii. r. esplits; et.
        rewrite T1. etrans.
        { eapply cmra_update_both_op; [refl|]. rewrite T1. refl. }
        sym. rewrite T1. etrans.
        { eapply cmra_update_both_op; [|refl]. rewrite T1. refl. }
        sym. rewrite assoc. refl. }
      { ii. r. esplits; et. rewrite T1. sym. rewrite T1. rewrite comm. refl. }
    - eapply RAX0plus_spec in U. des. r.
      split_l.
      { econs; ss; eauto.
        + econs; try refl.
        + ii. r in H. des. r. esplits; try sym; ss.
        + ii. r in H. r in H0. des. r. esplits; etrans; et.
      }
      split_l.
      { ii. r in H. des. r in H0. des. econs.
        + etrans. { eapply cmra_update_both_op; et. } refl.
        + rewrite T1. sym. rewrite T1.
          sym. etrans. { eapply cmra_update_both_op; et. } refl.
      }
      split_l.
      { ii. r in H. des. r in H. des.
        specialize (H ε). rewrite <- C5 in H0. rewrite <- C5. et. }
      esplits; ii; ss; et.
      { rr. esplits.
        - sym. rewrite C4; ss. refl.
        - eapply cmra_update_both_proper; et.
      }
      { rr. esplits.
        - sym. rewrite C5; ss. refl.
        - eapply cmra_update_both_proper; et.
      }
      { rr. esplits.
        - sym. rewrite C6; ss. refl.
        - erewrite <- T0. refl. }
  Qed.
  Next Obligation.
    ii; ss. des. eapply RAX1_spec in SAT. des. r in SAT0. des.
    r. esplits; et.
    { rewrite <- H4. refl. }
  Qed.
  Next Obligation.
    ii; ss. des. eapply RAX1_spec in SAT. des. r in SAT0. des.
    r. esplits; try refl.
  Qed.
  Next Obligation.
    ii; ss. des. eapply RAX1_spec in SAT. des. r in SAT0. des.
    r. esplits; try refl.
  Qed.
  Next Obligation.
    ii; ss.
  Qed.
  Next Obligation.
    i; ss.
  Qed.

  Global Program Instance replayable1: Replayable RAX0plus RAX1 := {
    rp_Hat := λ A, A;
    rp_hat := λ A a, a;
  }.
  Next Obligation.
    ii. des. rename H0 into C; r in C; des.
    eapply RAX0plus_spec in H. rename H into T. des; ss.
    split_l.
    - eapply RAX1_spec.
      split_l.
      { i. rewrite <- T0. refl. }
      split_l.
      { i. rewrite <- T1. refl. }
      split_l.
      { i. rewrite <- T2. refl. }
      split_l.
      { i. eapply cmra_update_both_equiv_subrel; eauto. }
      split_l.
      { r; i. rewrite assoc. refl. }
      { r; i. rewrite comm. refl. }
    - eapply RAX1_spec in U. des. r. esplits; ss.
  Qed.
  Next Obligation.
    ii; ss. des. eapply RAX0plus_spec in SAT. des. r in SAT0. des.
    refl.
  Qed.
  Next Obligation.
    ii; ss. des. eapply RAX0plus_spec in SAT. des. r in SAT0. des.
    refl.
  Qed.
  Next Obligation.
    ii; ss.
  Qed.
  Next Obligation.
    i; ss.
  Qed.

  Global Program Instance replayable2: Replayable RAX0plus RAX0 := {
    rp_Hat := λ A, A;
    rp_hat := λ A a, a;
  }.
  Next Obligation.
    ii. des. rename H0 into C; r in C; des.
    eapply RAX0plus_spec in H. rename H into T. des; ss.
    split_l.
    - eapply RAX0_spec.
      esplits; ss. ii. r in H. des. r. exists (core z). rewrite <- T2. eapply T. ss.
    - eapply RAX0_spec in U. des. r.
      esplits; ss.
  Qed.
  Next Obligation.
    ii; ss. des. eapply RAX0plus_spec in SAT. des. r in SAT0. des.
    refl.
  Qed.
  Next Obligation.
    ii; ss. des. eapply RAX0plus_spec in SAT. des. r in SAT0. des.
    refl.
  Qed.
  Next Obligation.
    ii; ss.
  Qed.
  Next Obligation.
    i; ss.
  Qed.

End RPL.




Class Ref (A : Type) := ref : A → A → Prop.
Global Hint Mode Ref ! : typeclass_instances.
Global Instance: Params (@op) 2 := {}.
Infix "⊑" := ref.
Notation "(⊑)" := ref (only parsing).

Definition ref_both `{Ref} := fun (a b: A) => a ⊑ b ∧ b ⊑ a.
Infix "⊒⊑" := ref_both (at level 50).
Notation "(⊒⊑)" := ref_both (only parsing).



(* MRA -> RAC *)
Section MRA.
  Local Set Default Proof Using "Type*".

  Context {A} `{EQV: Equiv A, OP: Op A, REF: Ref A, UNIT: Unit A}.
  Context `{EQUIVALENCE: Equivalence A (≡)}.
  Context `{op_proper : @Proper (A -> A -> A) ((≡) ==> (≡) ==> (≡)) (op)}.
  Context `{op_assoc : Assoc _ (≡) (@op A _)}.
  Context `{op_comm : Comm _ _ (≡) (@op A _)}.
  Context `{unit_idl: LeftId _ (≡) (ε: A) (⋅)}.
  Context `{ref_Proper: @Proper (A -> A -> Prop) ((≡) ==> (≡) ==> impl) (⊑)}.
  Context `{ref_preorder: PreOrder A (⊑)}.
  Context `{ref_hcomp: ∀ (a0 a1 b0 b1: A), a0 ⊑ b0 -> a1 ⊑ b1 -> (a0 ⋅ a1) ⊑ (b0 ⋅ b1)}.
  Context `{ref_affine: ∀ (a: A), a ⊑ ε}.
  Context `{CORE: PCore A}.
  Context `{core_intro: ∀ (a: A), a ≡ a ⋅ core a}.
  Context `{core_idemp: ∀ (a: A), core (core a) ≡ core a}.
  Context `{core_unit: (core (ε: A)) ≡ ε}.
  Context `{core_commute: ∀ (a b: A), core (a ⋅ b) ≡ core a ⋅ core b}.

  Variable (tgt: A).

  Global Program Instance Ref_Valid: Valid A := λ a, tgt ⊑ a.

  Lemma ref_fpu: ∀ (a b: A), (a ⊑ b) -> a ~~> b.
  Proof.
    i. r. ii. r in H0. r. unfold Ref_Valid in  *. etrans; et. eapply ref_hcomp; et. refl.
  Qed.

  Definition aProp := A -> Prop.
  Definition entails (P Q: aProp): Prop := ∀ a, P a -> Q a.
  Definition own (a: A): aProp := λ b, a ≼ b.
  Definition upd (P: aProp): aProp := λ b, ∀ fr, ✓ (fr ⋅ b) -> ∃ a, ✓ (fr ⋅ a) ∧ P a.

  Lemma incl_ref: ∀ (a b: A), a ≼ b -> b ⊑ a.
  Proof.
    i. rename H into T0.
    r in T0. des. eapply ref_Proper; [sym; apply T0| |].
    { instantiate (1:=a ⋅ ε). rewrite comm. eapply unit_idl. }
    eapply ref_hcomp; try refl.
    eapply ref_affine.
  Qed.

  Theorem logic_elim: ∀ src, (entails (own tgt) (upd (own src))) -> tgt ⊑ src.
  Proof.
    i. rr in H. unfold own in H.
    exploit (H tgt).
    { rr. exists ε. rewrite op_comm. rewrite unit_idl. refl. }
    { instantiate (1:=ε). r. unfold Ref_Valid.
      eapply ref_Proper; [refl| |]. { sym. apply unit_idl. } refl. }
    intro T; des. r in T. r in T. rewrite unit_idl in T. etrans; et.
    eapply incl_ref; et.
  Qed.

  Theorem logic_intro: ∀ a b, a ⊑ b -> (entails (own a) (upd (own b))).
  Proof.
    ii. unfold own in *.
    do 2 r in H1. esplits.
    2: { rr. exists ε. rewrite op_comm. rewrite unit_idl. refl. }
    do 2 r. etrans; et. eapply ref_hcomp; try refl.
    etrans; try apply H.
    eapply incl_ref; et.
  Qed.

  (* ra_validN_proper *)
  Goal @Proper (A -> Prop) (equiv ==> impl) valid.
  Proof.
    ii. do 2 r in H0. do 2 r. etrans; et. eapply ref_Proper.
    { sym; et. }
    { refl. }
    refl.
  Qed.

  (* ra_valid_op_l *)
  Goal ∀ x y : A, ✓ (x ⋅ y) → ✓ x.
  Proof.
    ii. do 2 r in H. do 2 r. etrans; et. eapply incl_ref. rr. esplits; et.
  Qed.

End MRA.
