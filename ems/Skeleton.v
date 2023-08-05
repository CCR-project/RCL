Require Import Coqlib.
Require Export ZArith.
Require Import String.
Require Export AList.

Set Implicit Arguments.

Local Open Scope nat_scope.

Notation gname := string (only parsing). (*** convention: not capitalized ***)




Fixpoint _find_idx {A} (f: A -> bool) (l: list A) (acc: nat): option (nat * A) :=
  match l with
  | [] => None
  | hd :: tl => if (f hd) then Some (acc, hd) else _find_idx f tl (S acc)
  end
.

Definition find_idx {A} (f: A -> bool) (l: list A): option (nat * A) := _find_idx f l 0.

Notation "'do' ' X <- A ; B" := (o_bind A (fun _x => match _x with | X => B end))
                                  (at level 200, X pattern, A at level 100, B at level 200)
                                : o_monad_scope.

Lemma find_idx_red {A} (f: A -> bool) (l: list A):
  find_idx f l =
  match l with
  | [] => None
  | hd :: tl =>
    if (f hd)
    then Some (0%nat, hd)
    else
      do (n, a) <- find_idx f tl;
      Some (S n, a)
  end.
Proof.
  unfold find_idx. generalize 0. induction l; ss.
  i. des_ifs; ss.
  - rewrite Heq0. ss.
  - rewrite Heq0. specialize (IHl (S n)). rewrite Heq0 in IHl. ss.
Qed.



Require Import Orders Permutation.

Module Sk.
  Class ld: Type := mk {
    t:> Type;
    equiv:> Equiv t;
    equiv_Equivalence:> Equivalence ((≡));
    unit: t;
    add :> OPlus t;
    wf: t -> Prop;
    add_comm: forall a b, (a ⊕ b) ≡ (b ⊕ a);
    add_assoc: forall a b c, a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ c;
    add_unit_l: forall a, unit ⊕ a = a;
    add_unit_r: forall a, a ⊕ unit = a;
    wf_comm: forall a b, wf (a ⊕ b) -> wf (b ⊕ a);
    unit_wf: wf unit;
    wf_equiv:> Proper ((≡) ==> impl) wf;
    add_equiv:> Proper ((≡) ==> (≡) ==> (≡)) add;
    extends := fun a b => exists ctx, (a ⊕ ctx) ≡ b;
    wf_mon: forall a b, extends a b -> wf b -> wf a;
  }
  .

  Global Program Instance add_OPlus `{ld}: OPlus t := add.

  Global Program Instance extends_PreOrder `{ld}: PreOrder extends.
  Next Obligation.
    ii. rr. exists unit. rewrite add_unit_r. refl.
  Qed.
  Next Obligation.
    ii. unfold extends in *. des. esplits; et. rewrite <- H1. rewrite <- H0. rewrite add_assoc. refl.
  Qed.

  Lemma extends_add: forall `{ld} a b c, extends a b -> extends (c ⊕ a) (c ⊕ b).
  Proof.
    ii. r in H0. des. r. esplits; et. rewrite <- add_assoc. rewrite H0. refl.
  Qed.

  Global Program Instance extends_Proper `{ld}: Proper ((≡) ==> (≡) ==> impl) extends.
  Next Obligation.
    ii. r in H2. des. r. esplits; et. rewrite <- H0. rewrite H2. ss.
  Qed.

  Global Program Instance extends_wf `{ld}: Proper ((extends) --> impl) wf.
  Next Obligation.
    ii. rr in H0. des. rewrite <- H0 in *. eapply wf_mon; et. r. esplits; et. refl.
  Qed.

  Global Program Instance add_extends_Proper `{ld}: Proper ((extends) ==> (extends) ==> (extends)) ((⊕)).
  Next Obligation.
    ii. etrans; et.
    { rewrite extends_add; et. refl. }
    { rewrite (add_comm x). rewrite (add_comm y). eapply extends_add; et. }
  Qed.

  (* Imp Instance *)
  Inductive gdef: Type := Gfun | Gvar (gv: Z).

  Module GDef <: Typ. Definition t := gdef. End GDef.
  Module SkSort := AListSort GDef.

  Definition sort: alist gname gdef -> alist gname gdef := SkSort.sort.

  Program Definition gdefs: ld :=
    @mk (alist gname gdef) (@Permutation _) _ nil (@List.app _)
      (fun sk => @List.NoDup _ (List.map fst sk)) _ _ _ _ _ _ _ _ _.
  Next Obligation.
    eapply Permutation_app_comm.
    (* econs; ii; ss. *)
    (* r in H. r in H0. r. *)
    (* rewrite H. ss. *)
  Qed.
  Next Obligation.
  Proof.
    eapply List.app_assoc.
  Qed.
  Next Obligation.
  Proof.
    unfold oplus.
    rewrite List.app_nil_r. auto.
  Qed.
  Next Obligation.
  Proof.
    i. eapply Permutation.Permutation_NoDup; [|et].
    eapply Permutation.Permutation_map.
    apply Permutation.Permutation_app_comm.
  Qed.
  Next Obligation.
  Proof.
    econs.
  Qed.
  Next Obligation.
    ii. r in H.
    eapply SkSort.sort_nodup in H0; et.
    eapply SkSort.sort_nodup; et. eapply Permutation_NoDup; try apply H0. eapply Permutation_map.
    rewrite <- ! SkSort.sort_permutation. ss.
  Qed.
  Next Obligation.
  Proof.
    rename b into c.
    rename H into b.
    cut (List.NoDup (map fst a)).
    { i. eapply Permutation.Permutation_NoDup; [|et].
      eapply Permutation.Permutation_map. refl.
    }
    cut (List.NoDup (map fst (a ++ b))).
    { i. rewrite map_app in H.
      eapply nodup_app_l. et. }
    i. eapply Permutation.Permutation_NoDup; [|et].
    eapply Permutation.Permutation_map.
    symmetry. rewrite H1. refl.
  Qed.

  Local Existing Instance gdefs.

  Definition sort_add_comm sk0 sk1
             (WF: wf (add sk0 sk1))
    :
      sort (add sk0 sk1) = sort (add sk1 sk0).
  Proof.
    eapply SkSort.sort_add_comm. eapply WF.
  Qed.

  Definition sort_wf sk (WF: wf sk):
    wf (sort sk).
  Proof.
    ss. eapply Permutation.Permutation_NoDup; [|apply WF].
    eapply Permutation.Permutation_map.
    eapply SkSort.sort_permutation.
  Qed.

End Sk.

Arguments Sk.unit: simpl never.
Arguments Sk.add: simpl never.
Arguments Sk.wf: simpl never.
