Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From Ordinal Require Import Ordinal Arithmetic.
Require Import SimSTS.

Set Implicit Arguments.


CoInductive conat: Type :=
| O: conat
| S: conat -> conat
.

Variant _is_even (is_even: conat -> Prop): conat -> Prop :=
| is_even_O: _is_even is_even O
| is_even_2: forall n, is_even n -> _is_even is_even (S (S n))
| is_even_4: forall n, is_even n -> _is_even is_even (S (S (S (S n))))
.

Definition is_even: _ -> Prop := paco1 _is_even bot1.

#[global] Hint Constructors _is_even.
Hint Unfold is_even.

Lemma is_even_mon: monotone1 _is_even.
Proof.
  ii. induction IN; ss; eauto.
Qed.

Hint Resolve is_even_mon: paco.


Variant _is_evenA (is_even: conat -> Prop): conat -> Prop :=
| is_even_AO: _is_evenA is_even O
| is_even_A2: forall n, is_even n -> _is_evenA is_even (S (S n))
.

Theorem is_evenA_spec1 r
  :
  paco1 _is_even r <1= _is_evenA (paco1 _is_even r)
.
Proof.
  i. punfold PR. induction PR.
  - econs; eauto.
  - r in H. des.
    + econs; eauto.
    + econs; eauto. admit "nooooooo".
  - r in H. des.
    + econs; eauto.
    + econs; eauto.
Qed.

Theorem is_evenA_spec2 r
  :
  paco1 _is_even r <1= _is_evenA (upaco1 _is_even r)
.
Proof.
  i. punfold PR. induction PR.
  - econs; eauto.
  - r in H. des.
    + econs; eauto.
    + econs; eauto.
  - r in H. des.
    + econs; eauto. left. eauto.
    + econs; eauto. econs; eauto.
Qed.

Variant _is_evenB (is_even: bool -> conat -> Prop): conat -> Prop :=
| is_even_BO: _is_evenB is_even O
| is_even_B4: forall n, is_even true n -> _is_evenB is_even (S (S (S (S n))))
| is_even_skip: forall n, is_even false n -> _is_evenB is_even n
.

Theorem is_evenB_spec r
  :
  paco1 _is_even r <1= _is_evenB (fun b => if b then upaco1 _is_even r else paco1 _is_even r)
.
Proof.
  i. punfold PR. induction PR.
  - econs; eauto.
  - r in H. des.
    + econs; eauto.
    + econs; eauto.
  - r in H. des.
    + econs; eauto.
    + econs; eauto.
Qed.

Reset _is_evenB.
(*** is_even_skip is too weak and the above theorems is meaningless.
```
Variant _is_evenB (is_even: bool -> conat -> Prop): conat -> Prop :=
| is_even_skip: forall n, is_even false n -> _is_evenB is_even n
.
```
Satisfies the theorem.
 ***)

Variant _is_evenB (condOn: bool) (is_even: conat -> Prop): conat -> Prop :=
| is_even_BO: _is_evenB condOn is_even O
| is_even_B4: forall n, (condOn -> is_even n) -> _is_evenB condOn is_even (S (S (S (S n))))
.
Reset _is_evenB.
(*** condOn looks hacky... what if the definition was given as follows ***)

Variant _is_evenB (is_even: conat -> Prop) (n: conat): Prop :=
| is_even_BO: (n = O) -> _is_evenB is_even n
| is_even_B4: (exists m, n = S (S (S (S m))) /\ is_even m) -> _is_evenB is_even n
.

Variant _is_evenB_cond: conat -> Prop :=
| is_even_cond_BO: _is_evenB_cond O
| is_even_cond_B4: forall n, _is_evenB_cond (S (S (S (S n))))
.

Notation "p -1> q" :=
  (fun x0 => forall (PR: p x0 : Prop), q x0 : Prop)
  (at level 50, no associativity).

Definition is_evenB (is_even: conat -> Prop) : conat -> Prop := _is_evenB_cond -1> _is_evenB is_even.

Theorem is_evenB_spec2 r
  :
  paco1 _is_even r <1= is_evenB (upaco1 _is_even r)
.
Proof.
  i. punfold PR. induction PR.
  - econs; eauto.
  - r in H. des.
    + ii. inv PR. econs 2; eauto. esplits; eauto. punfold H. dependent induction H; eauto.
    + ii. inv PR. econs 2; eauto. esplits; eauto. right. admit "??".
  - r in H. des.
    + econs 2; eauto.
    + econs 2; eauto.
Qed.



Section UPTO.
Variant twoC (r: conat -> Prop): conat -> Prop :=
| twoC_intro
    n
    (SIM: r (S (S n)))
  :
  twoC r n
.
Hint Constructors twoC: core.

Lemma twoC_mon
      r1 r2
      (LE: r1 <1= r2)
  :
    twoC r1 <1= twoC r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve twoC_mon: paco.

Lemma twoC_wrespectful: wrespectful1 (_is_even) twoC.
Proof.
  econs; eauto with paco.
  ii. inv PR. dup SIM. apply LE in SIM0.
  eapply GF in SIM.
  inv SIM.
  - destruct x0.
Admitted.

Lemma twoC_spec: twoC <2= gupaco1 (_is_even) (cpn1 (_is_even)).
Proof.
  intros. eapply wrespect1_uclo; eauto with paco. eapply twoC_wrespectful.
Qed.

Goal is_even (S O).
  ginit.
  { eapply cpn1_wcompat; eauto with paco. }
  gcofix CIH.
  guclo twoC_spec.
Qed.

Goal is_even (S O) -> False. i. punfold H. inv H. Qed.

End UPTO.




Module UPTOMINIMAL.

  Variant soundclo (clo: (conat -> Prop) -> (conat -> Prop)) : Prop := _soundclo
      (MON : monotone1 clo)
      (SOUND : forall r (PFIX: r <1= _is_even (clo r)), r <1= paco1 _is_even bot1)
  .
  Hint Constructors soundclo.

  Lemma clo_mon: forall clo, soundclo clo -> monotone1 (_is_even <*> clo).
  Proof. intros; destruct H; eauto using is_even_mon. Qed.
  Hint Resolve clo_mon : paco.

  Lemma soundclo_spec: forall clo (UPTO: soundclo clo),
      paco1 (_is_even <*> clo) bot1 <1= paco1 _is_even bot1.
  Proof.
    {
      i.
      inv UPTO. eapply (SOUND (paco1 (_is_even <*> clo) bot1)); [clear PR|exact PR].
      { i. punfold PR. rr in PR. eapply (@clo_mon clo); eauto. intros. pclearbot. ss. }
    }
    (* i; punfold PR; edestruct UPTO. *)
    (* eapply (SOUND (paco1 (_is_even <*> clo) bot1)); eauto. *)
    (* i; punfold PR0. *)
    (* { eapply (@clo_mon clo); eauto. intros; destruct PR1; eauto. ss. } *)
  Qed.




  Variant respectfulclo (clo: (conat -> Prop) -> (conat -> Prop)) : Prop := _respectfulclo
      (MON: monotone1 clo)
      (RESPECT: forall l r (LE: l <1= r) (SIM: l <1= _is_even r),
          clo l <1= _is_even (clo r)).
  Hint Constructors respectfulclo.

  Lemma respectfulclo_is_sound: forall clo, respectfulclo clo -> soundclo clo.
  Proof.
    set (rclo := fix rclo clo n (r: conat -> Prop) :=
           match n with
           | 0 => r
           | Datatypes.S n' => rclo clo n' r \1/ clo (rclo clo n' r)
           end).
    i; destruct H; econs; eauto. i.
    cut (forall n, rclo clo n r <1= _is_even (rclo clo (Datatypes.S n) r)).
    {
      set (rr a := exists n, rclo clo n r a).
      assert (rr x0) by (exists 0; eauto); clear PR.
      clear - H.
      i. revert x0 H. pcofix CIH. i.
      unfold rr in *. des. pfold. eapply is_even_mon.
      { eapply H0. eauto. }
      i. right. eapply CIH.
      { eexists. eapply PR. }
    }
    (* { intro X; revert x0 H; pcofix CIH; i. *)
    (*   unfold rr in *; des; eauto 10 using is_even_mon. } *)
    induction n; i; [by s; eauto using is_even_mon|].
    ss; des; [by eauto using is_even_mon|].
    eapply is_even_mon; [eapply RESPECT; [|apply IHn|]|]; inst; s; eauto.
  Qed.

  Variant gresclo (r: conat -> Prop) (x: conat) : Prop :=
    _gresclo clo (RES: respectfulclo clo) (CLO: clo r x)
  .
  Hint Constructors gresclo.

  Lemma respectful_compose: forall clo1 clo2 (RES1: respectfulclo clo1) (RES2: respectfulclo clo2),
      respectfulclo (clo1 <*> clo2).
  Proof. i; destruct RES1, RES2; eauto 10. Qed.

  Lemma gresclo_respectful: respectfulclo gresclo.
  Proof.
    econs; ii.
    - destructs IN RES; exists clo; eauto.
    - destructs PR RES; eapply is_even_mon with (r:=clo r); eauto.
  Qed.

  Lemma gres_mon: monotone1 (_is_even <*> gresclo).
  Proof.
    destruct gresclo_respectful; eauto using is_even_mon.
  Qed.
  Hint Resolve gres_mon : paco.

  Lemma gresclo_greatest: forall clo (RES: respectfulclo clo), clo <2= gresclo.
  Proof. eauto. Qed.

  Lemma gresclo_incl: forall r, r <1= gresclo r.
  Proof.
    i; eexists (fun x => x); eauto.
  Qed.
  Hint Resolve gresclo_incl.

  Lemma gresclo_compose: forall clo (RES: respectfulclo clo) r,
      clo (gresclo r) <1= gresclo r.
  Proof.
    i; eapply gresclo_greatest with (clo := clo <*> gresclo);
      eauto using respectful_compose, gresclo_respectful.
  Qed.

  (* Section TEST. *)
  (*   Variant gsoundclo (r: conat -> Prop) (x: conat) : Prop := *)
  (*     _gsoundclo clo (RES: soundclo clo) (CLO: clo r x) *)
  (*   . *)
  (*   Hint Constructors gsoundclo. *)

  (*   Lemma sound_compose: forall clo1 clo2 (RES1: soundclo clo1) (RES2: soundclo clo2), *)
  (*       soundclo (clo1 <*> clo2). *)
  (*   Proof. *)
  (*     i; destruct RES1, RES2. econs; eauto. i. exploit PFIX; eauto. intro T. *)
  (*     pfold. eapply is_even_mon; eauto. i. rr in PR0. left. *)
  (*     eapply SOUND. 2: { eapply PR0. } *)
  (*   Qed. *)

  (*   Lemma gsoundclo_respectful: respectfulclo gsoundclo. *)
  (*   Proof. *)
  (*     econs; ii. *)
  (*     - destructs IN RES; exists clo; eauto. *)
  (*     - destructs PR RES; eapply is_even_mon with (r:=clo r); eauto. *)
  (*   Qed. *)

  (*   Lemma gres_mon: monotone1 (_is_even <*> gsoundclo). *)
  (*   Proof. *)
  (*     destruct gsoundclo_respectful; eauto using is_even_mon. *)
  (*   Qed. *)
  (*   Hint Resolve gres_mon : paco. *)

  (*   Lemma gsoundclo_greatest: forall clo (RES: respectfulclo clo), clo <2= gsoundclo. *)
  (*   Proof. eauto. Qed. *)

  (*   Lemma gsoundclo_incl: forall r, r <1= gsoundclo r. *)
  (*   Proof. *)
  (*     i; eexists (fun x => x); eauto. *)
  (*   Qed. *)
  (*   Hint Resolve gsoundclo_incl. *)

  (*   Lemma gsoundclo_compose: forall clo (RES: respectfulclo clo) r, *)
  (*       clo (gsoundclo r) <1= gsoundclo r. *)
  (*   Proof. *)
  (*     i; eapply gsoundclo_greatest with (clo := clo <*> gsoundclo); *)
  (*       eauto using respectful_compose, gsoundclo_respectful. *)
  (*   Qed. *)
  (* End TEST. *)

End UPTOMINIMAL.





Module DOWNTO.

  Variant soundclo (clo: (conat -> Prop) -> (conat -> Prop)) : Prop := _soundclo
      (MON : monotone1 clo)
      (SOUND : forall r (PFIX: _is_even (clo r) <1= r), paco1 _is_even bot1 <1= r)
  .
  Hint Constructors soundclo.

  Lemma clo_mon: forall clo, soundclo clo -> monotone1 (_is_even <*> clo).
  Proof. intros; destruct H; eauto using is_even_mon. Qed.
  Hint Resolve clo_mon : paco.

  Lemma soundclo_spec: forall clo (UPTO: soundclo clo),
      paco1 _is_even bot1 <1= paco1 (_is_even <*> clo) bot1.
  Proof.
    {
      i.
      inv UPTO. eapply (SOUND (paco1 (_is_even <*> clo) bot1)); [clear PR|exact PR].
      { i. pfold. rr. eapply (@clo_mon clo); eauto. }
    }
  Qed.

  Goal soundclo twoC.
  Proof.
    econs.
    { ii. inv IN. econs; eauto. }
    i. punfold PR.
    (* assert(r x0 /\ r (S (S x0))). *)
    (* { induction PR; eauto. *)
    (*   - split; eauto. eapply PFIX. econs. econs. *)
    (* } *)
    induction PR; eauto.
    { pclearbot. punfold H. induction H.
  Abort.

  Goal soundclo (twoC \2/ id).
  Proof.
    econs.
    { ii. des.
      - left. inv IN. econs; eauto.
      - right. eauto. }
    i. punfold PR.
    assert(r x0 /\ r (S (S x0))).
    { destruct PR; eauto.
      - split; eauto. eapply PFIX. econs. right. r. eauto.
      - pclearbot. split; eauto.
        + eapply PFIX. econs. right. r. eauto. admit "???".
        + eapply PFIX. econs. right. r.
          eapply PFIX. econs. right. r.
  Abort.

End DOWNTO.
Reset DOWNTO.




Section DOWNTO.

  Variant soundclo (clo: (conat -> Prop) -> (conat -> Prop)) : Prop := _soundclo
      (MON : monotone1 clo)
      (* (SOUND : forall (u: (conat -> Prop) -> (conat -> Prop)), let r := paco1 (_is_even <*> u) bot1 in *)
      (*                    forall (PFIX: _is_even (clo r) <1= r), paco1 _is_even bot1 <1= r) *)
      (SOUND : let r := paco1 (_is_even <*> clo) bot1 in
               forall (PFIX: _is_even (clo r) <1= r), paco1 _is_even bot1 <1= r)
  .
  Hint Constructors soundclo.

  Lemma clo_mon: forall clo, soundclo clo -> monotone1 (_is_even <*> clo).
  Proof. intros; destruct H; eauto using is_even_mon. Qed.
  Hint Resolve clo_mon : paco.

  Lemma soundclo_spec: forall clo (UPTO: soundclo clo),
      paco1 _is_even bot1 <1= paco1 (_is_even <*> clo) bot1.
  Proof.
    {
      i.
      inv UPTO. eapply (SOUND); [clear PR|exact PR].
      { i. pfold. rr. eapply (@clo_mon clo); eauto. }
    }
  Qed.

  Variant lsoundclo (r: conat -> Prop) (x: conat) : Prop :=
    _lsoundclo (LEAST: forall clo (RES: soundclo clo), <<CLO: clo r x>>)
  .
  Hint Constructors lsoundclo.

  (* Lemma sound_compose: forall clo1 clo2 (RES1: soundclo clo1) (RES2: soundclo clo2), *)
  (*     soundclo (clo1 <*> clo2). *)
  (* Proof. *)
  (*   i; destruct RES1, RES2. econs; eauto. i. exploit PFIX; eauto. intro T. *)
  (*   pfold. eapply is_even_mon; eauto. i. rr in PR0. left. *)
  (*   eapply SOUND. 2: { eapply PR0. } *)
  (* Qed. *)

  Lemma lsound_mon: monotone1 (_is_even <*> lsoundclo).
  Proof.
    ii. unfold compose in *. eapply is_even_mon; eauto. ii. inv PR. econs. ii. inv RES. eapply MON; eauto. eapply LEAST. eauto.
  Qed.
  Hint Resolve lsound_mon : paco.

  Lemma lsoundclo_least: forall clo (RES: soundclo clo), lsoundclo <2= clo.
  Proof. i. inv PR. eapply LEAST. eauto. Qed.

  Lemma lsoundclo_id: lsoundclo <2= id.
  Proof.
    ii. r. inv PR. eapply LEAST. eauto.
  Qed.
  Hint Resolve lsoundclo_id.

  Lemma lsoundclo_idem: (lsoundclo) <2= lsoundclo <*> lsoundclo.
  Proof.
    ii. rr. inv PR. econs.
    ii. r. eapply LEAST. inv RES.
    econs.
  Qed.

  Lemma twoC_sound: soundclo twoC.
  Proof.
    econs.
    { ii. inv IN. econs; eauto. }
    i. subst r. revert_until PFIX. pcofix CIH. i. punfold PR.
    pfold. rr. eapply is_even_mon; eauto. i. pclearbot.
    econs. right. eapply CIH. eauto.
  Qed.

End DOWNTO.


Theorem is_evenB_spec2_extrapolate r gclo
                                   (MON: monotone1 (_is_even <*> gclo))
  :
  paco1 (_is_even <*> gclo) r <1= is_evenB (upaco1 (_is_even <*> gclo) r)
.
Proof.
  i. punfold PR. rr in PR. destruct PR.
  - econs; eauto.
  - r in H. des.
    + ii. inv PR. econs 2; eauto. esplits; eauto. punfold H. dependent induction H; eauto.
    + ii. inv PR. econs 2; eauto. esplits; eauto. right. admit "??".
  - r in H. des.
    + econs 2; eauto.
    + econs 2; eauto.
  i. punfold PR.
  - econs; eauto.
  - inv H. r in SIM. des.
    + ii. inv PR. econs 2; eauto. esplits; eauto. punfold SIM. 2: { admit "ez". } rr in SIM.
      dependent induction SIM; eauto.
      { inv H. pclearbot.
    + ii. inv PR. econs 2; eauto. esplits; eauto. right. admit "??".
  - r in H. des.
    + econs 2; eauto.
    + econs 2; eauto.
Qed.

  (* Variant respectfulclo (clo: (conat -> Prop) -> (conat -> Prop)) : Prop := _respectfulclo *)
  (*     (MON: monotone1 clo) *)
  (*     (RESPECT: forall l r (LE: l <1= r) (SIM: _is_even l <1= r), *)
  (*         _is_even (clo r) <1= clo l). *)
  (* Hint Constructors respectfulclo. *)

  (* Lemma respectfulclo_is_sound: forall clo, respectfulclo clo -> soundclo clo. *)
  (* Proof. *)
  (*   { *)
  (*     i. destruct H. econs; eauto. i. *)
  (*     punfold PR. *)
  (*   } *)
  (*   set (rclo := fix rclo clo n (r: conat -> Prop) := *)
  (*          match n with *)
  (*          | 0 => r *)
  (*          | Datatypes.S n' => rclo clo n' r \1/ clo (rclo clo n' r) *)
  (*          end). *)
  (*   i; destruct H; econs; eauto. i. *)
  (*   cut (forall n, rclo clo n r <1= _is_even (rclo clo (Datatypes.S n) r)). *)
  (*   { *)
  (*     set (rr a := exists n, rclo clo n r a). *)
  (*     assert (rr x0) by (exists 0; eauto); clear PR. *)
  (*     clear - H. *)
  (*     i. revert x0 H. pcofix CIH. i. *)
  (*     unfold rr in *. des. pfold. eapply is_even_mon. *)
  (*     { eapply H0. eauto. } *)
  (*     i. right. eapply CIH. *)
  (*     { eexists. eapply PR. } *)
  (*   } *)
  (*   induction n; i; [by s; eauto using is_even_mon|]. *)
  (*   ss; des; [by eauto using is_even_mon|]. *)
  (*   eapply is_even_mon; [eapply RESPECT; [|apply IHn|]|]; inst; s; eauto. *)
  (* Qed. *)
