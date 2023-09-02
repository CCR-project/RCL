Require Import Coqlib.
Require Export sflib.
Require Export AList.
Require Import Skeleton.
Require Import Algebra.
Require Import ModSem Mod ModSemFacts ModFacts.
Require Import HTactics.

Require Import IPM.

Set Implicit Arguments.

Section AUX.

  Context `{Sk.ld}.

  Definition OwnM (m: Mod.t) : (@mProp (MRA_to_MRAS (Mod_MRA))) :=
    Own ((m: Mod_MRA.(MRA.car)) : (MRA_to_MRAS Mod_MRA).(MRAS.car)).

End AUX.
