Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.

Set Implicit Arguments.



Section PROOF.

  Definition fF: list val -> itree Es val :=
    fun varg => b <- trigger (Take bool);; Ret b.

  Definition FSem: ModSem.t := {|
    ModSem.fnsems := [("f", cfunU fF)];
    ModSem.mn := "F";
    ModSem.initial_st := tt↑;
  |}
  .

  Definition F: Mod.t := {|
    Mod.get_modsem := fun _ => FSem;
    Mod.sk := [("f", Sk.Gfun)];
  |}
  .
End PROOF.
