Require Import Coqlib.
From stdpp Require Import base.

Set Implicit Arguments.

Record path (A B: Type): Type := mk_path {
  to:> A -> B;
  from: B -> A;
  (* correct1: from ∘ to = id; *)
  (* correct2: to ∘ from = id; *)
  correct1: ∀ x, from (to x) = x;
  correct2: ∀ x, to (from x) = x;
}.

Definition path_id: ∀ A, path A A.
Proof.
  i. eapply (@mk_path _ _ id id); ss.
Defined.

Definition path_sym: ∀ A B, path A B -> path B A.
Proof.
  i. eapply (@mk_path _ _ X.(from) X.(to)); ss.
  - destruct X. ss.
  - destruct X. ss.
Defined.

Definition path_comm: ∀ A B, path (A * B) (B * A).
Proof.
  i. eapply (@mk_path _ _ (fun ab => (ab.2, ab.1)) (fun ab => (ab.2, ab.1))); ss.
  - i. destruct x; ss.
  - i. destruct x; ss.
Defined.

Definition path_assoc: ∀ A B C, path (A * (B * C)) ((A * B) * C).
Proof.
  i. eapply (@mk_path _ _ (fun abc => ((abc.1, abc.2.1), abc.2.2))
               (fun abc => (abc.1.1, (abc.1.2, abc.2)))); ss.
  - i. destruct x; ss. destruct p; ss.
  - i. destruct x; ss. destruct p; ss.
Defined.

Definition path_trans: ∀ A B C, path A B -> path B C -> path A C.
Proof.
  (* i. destruct X, X0; ss. *)
  (* eapply (@mk_path _ _ (to1 ∘ to0) (from0 ∘ from1)); ss. *)
  (* - change (from0 ∘ from1 ∘ (to1 ∘ to0)) with (from0 ∘ (from1 ∘ to1) ∘ to0). *)
  (*   i. rewrite correct5. rewrite <- correct3. reflexivity. *)
  (* - change (to1 ∘ to0 ∘ (from0 ∘ from1)) with (to1 ∘ (to0 ∘ from0) ∘ from1). *)
  (*   i. rewrite correct4. rewrite <- correct6. reflexivity. *)
  i.
  eapply (@mk_path _ _ (X0.(to) ∘ X.(to)) (X.(from) ∘ X0.(from))); ss.
  - i. rewrite correct1. rewrite correct1. reflexivity.
  - i. rewrite correct2. rewrite correct2. reflexivity.
Defined.

Definition path_unitl: ∀ A, path (unit * A) A.
Proof.
  i. eapply (@mk_path _ _ (fun ta => ta.2) (fun a => (tt, a))); ss.
  - i. destruct x; ss. des_u; ss.
Defined.

Definition path_unitr: ∀ A, path (A * unit) A.
Proof.
  i. eapply (@mk_path _ _ (fun ta => ta.1) (fun a => (a, tt))); ss.
  - i. destruct x; ss. des_u; ss.
Defined.

Definition path_combine: ∀ A0 A1 B0 B1,
    path A0 B0 -> path A1 B1 -> path (A0 * A1) (B0 * B1).
Proof.
  i. eapply (@mk_path _ _ (fun a => (X a.1, X0 a.2))
               (fun b => (X.(from) b.1, X0.(from) b.2))); ss.
  - i. destruct x; ss. rewrite ! correct1; refl.
  - i. destruct x; ss. rewrite ! correct2; refl.
Defined.


