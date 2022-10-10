Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import ProofMode.

Set Implicit Arguments.


Module Bipartite.

  Variant car: Type :=
    | a: car
    | b: car
    | c: car
    | x: car
    | y: car
    | z: car
    | _ax: car
    | _ay: car
    | _bx: car
    | _by: car
    | _bz: car
    | _cy: car
    | _cz: car
    | unit: car
    | boom: car
  .
  Definition add: car -> car -> car :=
    fun c0 c1 =>
      match c0, c1 with
      | a, x => _ax
      | x, a => _ax
      | a, y => _ay
      | y, a => _ay
      | b, x => _bx
      | x, b => _bx
      | b, y => _by
      | y, b => _by
      | b, z => _bz
      | z, b => _bz
      | c, y => _cy
      | y, c => _cy
      | c, z => _cz
      | z, c => _cz
      | unit, _ => c1
      | _, unit => c0
      | _, _ => boom
      end
  .

  Program Instance ce_pcm: URA.t := {
      car := car;
      unit := unit;
      _add := add;
      _wf := fun c => c <> boom;
      core := fun _ => unit;
  }.
  Next Obligation. i. destruct a0, b0; ss. Qed.
  Next Obligation. i. destruct a0, b0, c0; ss. Qed.
  Next Obligation. i. rewrite Seal.sealing_eq. destruct a0; ss. Qed.
  Next Obligation. i. rewrite Seal.sealing_eq. ss. Qed.
  Next Obligation. i. rewrite ! Seal.sealing_eq in *. destruct a0, b0; ss. Qed.
  Next Obligation. i. rewrite ! Seal.sealing_eq in *. destruct a0; ss. Qed.
  Next Obligation. i. ss. Qed.
  Next Obligation. i. rewrite ! Seal.sealing_eq in *. esplits; eauto. Qed.

End Bipartite.
