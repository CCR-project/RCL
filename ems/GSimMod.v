Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import Mod ModSem.
Require Import Skeleton.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From Ordinal Require Import Ordinal Arithmetic.
Require Import SimSTS SimModSemGlobal.

Set Implicit Arguments.


Variable md_src md_tgt: Mod.t.
Let ms_src: ModSem.t := md_src.(Mod.enclose).
Let ms_tgt: ModSem.t := md_tgt.(Mod.enclose).

Section ADEQUACY.
Hypothesis (SIM: simg eq false false (@ModSem.initial_itr ms_src CONFS (Some (Mod.wf md_src))) (@ModSem.initial_itr ms_tgt CONFT (Some (Mod.wf md_tgt)))).


Theorem adequacy_global: Beh.of_program (@Mod.compile _ CONFT md_tgt) <1= Beh.of_program (@Mod.compile _ CONFS md_src).
Proof.
  eapply adequacy_global_itree. eapply SIM.
Qed.
End ADEQUACY.
