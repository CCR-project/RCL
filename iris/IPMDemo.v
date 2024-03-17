Require Import Algebra Coqlib.
Require Import String RCLIPM.
Set Implicit Arguments.
Open Scope string_scope.
Open Scope list_scope.



Section TUTORIAL.

Context `{M: MRAS.t}.
Goal ∀ (a0 a1 b0 b1 c0 c1: mProp),
    (a0 ==∗ a1) -> ((a1 ∗ b0) ==∗ (a1 ∗ b1)) -> ((a1 ∗ c0) ==∗ (a1 ∗ c1))
    -> ((a0 ∗ b0 ∗ c0) ==∗ (a1 ∗ b1 ∗ c1))
.
Proof.
  i.
  {
    iIntros "[? [? ?]]".
    iDestruct (H with "[$]") as ">?". iDestruct (H0 with "[$]") as ">[? $]".
    iDestruct (H1 with "[$]") as "$".
  }
Qed.


Goal forall a0 a1 b0 b1 c0 c1,
    a0 ⊑ a1 -> a1 ⊕ b0 ⊑ a1 ⊕ b1 -> a1 ⊕ c0 ⊑ a1 ⊕ c1 ->
    a0 ⊕ b0 ⊕ c0 ⊑ a1 ⊕ b1 ⊕ c1.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  erewrite oplus_comm_weak with (b:=c0).
  erewrite <- oplus_comm_weak with (a:=c1).
  rewrite oplus_assoc_weak2.
  rewrite oplus_assoc_weak2.
  apply ref_oplus; [|reflexivity].
  erewrite oplus_comm_weak with (b:=a1).
  erewrite <- oplus_comm_weak with (b:=c1).
  rewrite H1.
  reflexivity.
Qed.
End TUTORIAL.
