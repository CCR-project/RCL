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

(*
inf, ?
?, inf
fin & even, fin & even
*)
Variant _is_even (is_even: conat -> conat -> Prop): conat -> conat -> Prop :=
| is_even_O: _is_even is_even O O
| is_even_l: forall n m, is_even n m -> _is_even is_even (S (S n)) m
| is_even_r: forall n m, is_even n m -> _is_even is_even n (S (S m))
.

Definition is_even: _ -> _ -> Prop := paco2 _is_even bot2.

#[global] Hint Constructors _is_even.
Hint Unfold is_even.

Lemma is_even_mon: monotone2 _is_even.
Proof.
  ii. induction IN; ss; eauto.
Qed.
Hint Resolve is_even_mon: paco.

Section CONT.
  Variable T0 : Type.
  Variable T1 : forall (x0: @T0), Type.

  Definition cont2 (gf: rel2 T0 T1 -> rel2 T0 T1) :=
    forall x0 x1 A B (IN: gf (A \2/ B) x0 x1), (gf A \2/ gf B) x0 x1.

  Definition cont2_rev (gf: rel2 T0 T1 -> rel2 T0 T1) :=
    forall x0 x1 A B (IN: (gf A \2/ gf B) x0 x1), gf (A \2/ B) x0 x1.

  Lemma mono_cont2_rev gf (MON: monotone2 gf): cont2_rev gf.
  Proof. ii. des; eapply MON; eauto. Qed.
End CONT.

Lemma is_even_cont: cont2 _is_even.
Proof.
  ii. inv IN; eauto.
  - des.
    + left. econs; eauto.
    + right. econs; eauto.
  - des.
    + left. econs; eauto.
    + right. econs; eauto.
Qed.

Notation "p -2> q" :=
  (fun x0 x1 => forall (PR: p x0 x1 : Prop), q x0 x1 : Prop)
  (at level 51, right associativity).
Notation "p -3> q" :=
  (fun x0 x1 x2 => forall (PR: p x0 x1 x2 : Prop), q x0 x1 x2 : Prop)
  (at level 51, right associativity).

Definition _is_evenL (is_even: conat -> conat -> Prop) (n m: conat): Prop :=
  (exists n', n = S (S n') /\ is_even n' m)
.

Section MINKI.
  Definition _is_evenL_e (is_even: conat -> conat -> Prop) (n m: conat): Prop :=
    is_even (S (S n)) m.

  Lemma WRES: wrespectful2 _is_even _is_evenL.
  Proof.
    econs; eauto.
    { admit "ez". }
    i. inv PR. des. subst.
    econs; eauto. eapply rclo2_base. eauto.
  Qed.

  Lemma WRES_e: wrespectful2 _is_even _is_evenL_e.
  Proof.
    econs; eauto.
    { admit "ez". }
    i. (* set (N:=x0). set(m:=x1). *)
    r in PR. dup PR. eapply GF in PR. eapply LE in PR0. inv PR.
    { (* unprovable when x0 = 1 *)
      admit "??". }
  Abort.

  Goal _is_evenL_e <*> (cpn2 _is_even) <3= (cpn2 _is_even).
  Proof.
    ii. r in PR. eapply cpn2_cpn.
    { admit "ez". }
    eapply wrespect2_companion; eauto.
    { admit "ez". }
  (*   { eapply WRES. } *)
  (*   r in PR. *)
  (* Qed. *)
  Abort.

End MINKI.

Definition _is_evenL_cond (n m: conat): Prop := (exists n', n = S (S n')).

Definition is_evenL (is_even: conat -> conat -> Prop) : conat -> conat -> Prop := _is_evenL_cond -2> _is_evenL is_even.

Lemma compat
  :
  is_evenL <*> _is_even <3= _is_even <*> is_evenL
.
Proof.
  ii. unfold compose in *.
  rr in PR.
  (* if x1 is (S O), it does not help here. *)
Abort.

Lemma decompat
  :
  _is_even <*> is_evenL <3= is_evenL <*> _is_even
.
Proof.
  ii. unfold compose in *.
  rr in PR0. des. subst.
  rr. esplits; eauto.
  inv PR; ss.
  (* if n' is not even it does not hold *)
Abort.

(* maybe the theory needs to recognize conditions? *)

Lemma decompat
  :
  (_is_even \3/ id) <*> _is_evenL <3= _is_evenL <*> (_is_even \3/ id)
.
Abort.
(* it does not help *)

Lemma decompat
  :
  (* forall r n m (COND: _is_evenL_cond n m), ((_is_even <*> _is_evenL) r n m) <0= ((_is_evenL <*> _is_even) r n m) *)
  ((fun _ => _is_evenL_cond) /3\ ((_is_even <*> _is_evenL)) <3= (_is_evenL <*> _is_even))
.
Proof.
  i. unfold compose in *. des.
  inv PR.
  rr. esplits; eauto.
  inv PR0; ss.
  - rr in H0. des. subst. econs; eauto.
  - rr in H. des. clarify. econs; eauto.
Qed.

Lemma compat
  :
  forall r n m (COND: _is_evenL_cond n m), ((_is_evenL <*> _is_even) r n m) <0= ((_is_even <*> _is_evenL) r n m)
.
Proof.
  i. unfold compose in *.
  inv COND.
  rr in PR. des. clarify. inv PR0.
  - econs; eauto. econs; eauto. Abort.


Theorem is_evenL_simpl
  :
  paco2 _is_even bot2 <2= is_evenL (upaco2 _is_even bot2)
.
Proof.
  i. punfold PR. induction PR.
  - ii. rr in PR. des; ss.
  - r in H. des; ss.
    + ii. inv PR. clarify. econs; eauto.
  - r in H. des; ss.
    + ii. inv PR. r. esplits; eauto. left.
      { revert_until m. revert m. pcofix CIH.
        i. punfold H0. inv H0.
        - r in H1. des; ss.
          { pfold. econs; eauto. left. eapply paco2_mon; eauto. ii; ss. }
        - r in H. des; ss.
          { pfold. econs; eauto. }
      }
Qed.

Theorem is_evenB_spec2
  r
  :
  paco2 _is_even r <2= is_evenL (upaco2 _is_even r)
.
Proof.
  i. punfold PR. induction PR.
  - ii. rr in PR. des; ss.
  - r in H. des.
    + ii. inv PR. clarify. econs; eauto.
    + ii. inv PR. clarify. econs; eauto.
  - r in H. des.
    + ii. inv PR. r. esplits; eauto. left.
      { revert_until r. pcofix CIH.
        i. punfold H0. inv H0.
        - r in H1. des.
          { pfold. econs; eauto. left. eapply paco2_mon; eauto. }
          { pfold. econs; eauto. }
        - r in H. des.
          { pfold. econs; eauto. }
          { pfold. econs; eauto. right. eapply CIH.
            pfold. econs; eauto. left. admit "??? do we need respectful?".
          }
      }
    + ii. rr in PR. des; subst. rr. esplits; eauto. left. pfold. econs; eauto.
Abort.

(*
y <= ftx      f compat (f <= t)
----------------------------------
y <= tx


y <= ux
----------------------------------
y <= fux      f dcompat (f <= u)
*)


Module THEORY. Section THEORY.
  Variable T0 : Type.
  Variable T1 : forall (x0: @T0), Type.

  Local Notation rel := (rel2 T0 T1).

  Variable gf: rel -> rel.
  Hypothesis gf_mon: monotone2 gf.

  Goal cpn2 gf = cpn2 (gf /3\ id).
  Proof.
    assert(Y: cpn2 gf <3= cpn2 (gf /3\ id)).
    { i. inv PR. econs; eauto. inv COM. econs; eauto.
      ii. split.
      + eapply compat2_compat; eauto. eapply compat2_mon; eauto. ii. ss; des; ss.
      + rr. eapply compat2_mon; eauto. ii. ss; des; ss.
    }
    extensionality r.
    extensionality x0.
    extensionality x1.
    assert(MON': monotone2 (gf /3\ id)).
    { ii. des. esplits; et. }
    apply prop_ext.
    split; i; et.
    - eapply cpn2_greatest; eauto. econs; eauto.
      { eapply cpn2_mon; eauto. }
      clear H. clear x1. clear x0. clear r.
      assert(T: gf <3= (gf /3\ id) <*> cpn2 gf).
      { ii. rr. split; i.
        - eapply gf_mon; eauto. ii. eapply cpn2_base; eauto.
        - rr. eapply cpn2_step; eauto. eapply gf_mon; eauto. ii. eapply cpn2_base; et.
      }
      ii.
      assert(U: (cpn2 (gf /3\ id) <*> (gf /3\ id) <*> cpn2 gf) r x0 x1).
      { eapply cpn2_mon; eauto. eapply T. }
      assert(V: ((gf /3\ id) <*> cpn2 (gf /3\ id) <*> cpn2 gf) r x0 x1).
      { assert(X:=cpn2_compat MON'). inv X. eapply compat2_compat in U. eauto. }
      assert(W: ((gf /3\ id) <*> cpn2 (gf /3\ id) <*> cpn2 (gf /3\ id)) r x0 x1).
      { eapply MON'; eauto. i. eapply cpn2_mon; eauto. }
      assert(X: ((gf /3\ id) <*> cpn2 (gf /3\ id)) r x0 x1).
      { eapply MON'; eauto. i. eapply cpn2_cpn; eauto. }
      rr in X. des; ss.
  Qed.

  Structure dcompatible2 (clo: rel -> rel) : Prop :=
    dcompat2_intro {
        dcompat2_mon: monotone2 clo;
        dcompat2_dcompat : forall r,
          gf (clo r) <2= clo (gf r);
      }.
  
  Variant cpn2 (r: rel) x0 x1 : Prop :=
  | cpn2_intro
      clo
      (COM: compatible2 gf clo)
      (CLO: clo r x0 x1)
  .
  Check (cpn2: rel -> rel).

  (* Variant U (R: rel -> rel) r x0 x1 : Prop := *)
  (* | cpn2_intro *)
  (*     clo *)
  (*     (COM: compatible2 gf clo) *)
  (*     (CLO: clo r x0 x1) *)
  (* . *)

End THEORY. End THEORY.

From Ordinal Require Import ClassicalOrdinal.

(*
tx = ⋁_{u f ≤ f u} u
Goal: ∀ x. tx = ⋀_{x ≤ f_a} f_a

(i) ∀ x. tx ≤ ⋀_{x ≤ f_a} f_a
<=> ∀ x a, x ≤ f_a -> tx ≤ f_a
<=> ∀ x a u, x ≤ f_a -> (uf ≤ fu) -> ux ≤ f_a

uf ≤ fu
--------------------------
∀ a x, x ≤ f_a -> ux ≤ f_a

Use transifinite induction on a.
- a = O. trivial. ∎
- a = S b.
  IH: ∀ x. x ≤ f_b -> ux ≤ f_b
  WTS: ∀ x. x ≤ f f_b -> ux ≤ f f_b
  ux ≤ u f f_b (by premise)
     ≤ f u f_b (by compat)
     ≤ f f_b (by IH, put x <-| f_b) ∎
- a = λ.
  IH: ∀ x o. o < λ -> x ≤ f_o -> ux ≤ f_o
  WTS: ∀ x. x ≤ (⋀_{o < λ} f_o) -> ux ≤ (⋀_{o < λ} f_o)
  ux ≤ u (⋀_{o < λ} f_o) (by premise)
  ETS. u (⋀_{o < λ} f_o) ≤ (⋀_{o < λ} f_o)
<=> ∀ o < λ. u (⋀_{o < λ} f_o) ≤ f_o
<=  ∀ o < λ. u f_o ≤ f_o (SCOTT-CONT exploited?!)
This holds by IH (put x <-| f_o). ∎

(ii)
It suffices to show (fun x -> ⋀_{x ≤ f_a} f_a) is compatible.
(fun x -> ⋀_{x ≤ f_a} f_a) f ≤ f (fun x -> ⋀_{x ≤ f_a} f_a)
<=> ∀ x. ⋀_{f x ≤ f_a} f_a ≤ f (⋀_{x ≤ f_a} f_a)

It is known that
(not exactly this form, but the idea of using Hartog's number will apply here too: https://arxiv.org/pdf/1605.04136.pdf)
such a sequence is stationary (it has its limit on the sequence itself).
let f_ε0 := ⋀_{f x ≤ f_a}.
let f_ε1 := ⋀_{x ≤ f_a}.
Now, ETS: ∀ x. f_ε0 ≤ f f_ε1 = f_(S ε1)
Now, either ε0 ≤ S ε1 or S ε1 ≤ ε0 holds.
In either case, it is known that (by transfinite induction) (∀ ε0 ≤ 𝛼. f_ε0 = f_𝛼) and (∀ ε1 ≤ 𝛼. f_ε1 = f_𝛼). ∎


---------------------------------------------scratch------------------------------------------------


(ii) ∀ x. ⋀_{x ≤ f_a} f_a ≤ tx
<=  ∀ x. (⋀_{x ≤ f_a} f_a) f ≤ f (⋀_{x ≤ f_a} f_a) (by greatest-compat)
<=  ∀ x a. x ≤ f_a. f_a f ≤ f f_a

Use transfinite induction on a.
- a = O. ⊤ f ≤ f ⊤. ?? type error.


(ii) ∀ x. ⋀_{x ≤ f_a} f_a ≤ tx
First, we have: 𝜈f = t⊥ ≤ tx.
Thus, it suffices to show:
∀ x. ⋀_{x ≤ f_a} f_a ≤ 𝜈f
By Kleene's fixpoint theorem (Cousot's version), we have
𝜈f = ⋀ f_a... dead end.
*)

(*
Goal: ∀ d. f d ≤ d f -> tx ≤ dtx
First, unfold tx with Kleene-style stratification.
ETS: ⋀_{x ≤ f_a} f_a ≤ d ⋀_{x ≤ f_a} f_a
<=> f_ε ≤ d f_ε


∀ u. u f ≤ f u -> utx ≤ tx
u f^o ⊤ <= f^o (u ⊤) ≤ f^o ⊤

dead end...

y ≤ tx -> y ≤ dtx
<=> (∀ x ≤ f_a, y ≤ f_a) -> y ≤ d ⋀_{x ≤ f_a} f_a

∀ x ≤ f_a. y ≤ f_a <=> y ≤ ⋀_{x ≤ f_a} f_a
*)

(*
Q: Dx = ⋁_{f_a ≤ x} f_a (starting from bot)??
이게 성립하면 U/D 저렇게 하는거는 dead end 일 것이고.

S case에 f 앞에 붙이냐 뒤에 붙이냐도 다를려나? 뒤에 붙이면 그건 뭐지...

knowledge 안에 D를 칠해놓는 방법을 생각해봐야 할 것 같음.
*)

(*
Dx = ⋀_{f d ≤ d f} d
Goal: ∀ x. Dx = ⋁_{f_a ≤ x} f_a

f_a := match a with
       | O => ⊥
       | S b => f f_b
       | λ => ⋁_{𝛼 ≤ λ} f_𝛼

(i) ∀ x. Dx ≤ ⋁_{f_a ≤ x} f_a
It suffices to show (fun x -> ⋁_{f_a ≤ x} f_a) is dcompatible.
f (fun x -> ⋁_{f_a ≤ x} f_a) ≤ (fun x -> ⋁_{f_a ≤ x} f_a) f
<=> ∀ x. f (⋁_{f_a ≤ x} f_a) ≤ ⋁_{f_a ≤ f x} f_a

It is known that
(not exactly this form, but the idea of using Hartog's number will apply here too: https://arxiv.org/pdf/1605.04136.pdf)
such a sequence is stationary (it has its limit on the sequence itself).
let f_ε0 := ⋁_{f_a ≤ x}.
let f_ε1 := ⋁_{f a ≤ f_x}.
Now, ETS: ∀ x. f_(S ε0) = f f_ε0 ≤ f_ε1
Now, either S ε0 ≤ ε1 or ε1 ≤ S ε0 holds.
In either case, it is known that (by transfinite induction) (∀ ε0 ≤ 𝛼. f_ε0 = f_𝛼) and (∀ ε1 ≤ 𝛼. f_ε1 = f_𝛼). ∎

Q: 무슨 무슨 성질을 쓴거지..? ∀ x. Ux ≤ ⋁_{f_a ≤ x} f_a 는 성립 안해야 할텐데 어디서 막히지?
A: RHS가 compatible하다는거 보이면 RHS <= Ux가 됨...

(ii) ∀ x. ⋁_{f_a ≤ x} f_a ≤ Dx
<=> ∀ x a, f_a ≤ x -> f_a ≤ Dx
<=> ∀ x a d, f a ≤ x -> (fd ≤ df) -> f_a ≤ dx

fd ≤ df
--------------------------
∀ a x, f a ≤ x -> f_a ≤ dx

Use transifinite induction on a.
- a = O. trivial. ∎
- a = S b.
  IH: ∀ x. f_b ≤ x -> f_b ≤ dx
  WTS: ∀ x. f f_b ≤ x -> f f_b ≤ dx
  dx ≥ d f f_b (by premise)
     ≥ f d f_b (by dcompat)
     ≥ f f_b (by IH, put x <-| f_b) ∎
- a = λ.
  IH: ∀ x o. o < λ -> f_o ≤ x -> f_o ≤ dx
  WTS: ∀ x. (⋁_{o < λ} f_o) ≤ x -> (⋀_{o < λ} f_o) ≤ dx
  dx ≥ d (⋁_{o < λ} f_o) (by premise)
  ETS. d (⋁_{o < λ} f_o) ≥ (⋁_{o < λ} f_o)
<=> ∀ o < λ. d (⋀_{o < λ} f_o) ≥ f_o
<=  ∀ o < λ. d f_o ≤≥ f_o (SCOTT-CONT exploited?!)
This holds by IH (put x <-| f_o). ∎
*)
u f_ε x ≤ f_ε x
<= f_ε u x ≤ f_ε x (transifinite induction, compat)≤ 

Section TREC.
  Variable D: Type.
  Variable base: D.
  Variable next: D -> D.
  (* Variable djoin: forall (λ: Ord.t) (ds: { o: Ord.t | (o < λ)%ord } -> D), D. *)
  Variable djoin: forall (ds: Ord.t -> D), D.

  (* Let dunion (d0 d1: D): D := djoin (fun b: bool => if b then d0 else d1). *)

  Fixpoint trec (o: Ord.t): D :=
    match o with
    | @Ord.build X os =>
        (* dunion base *)
          (djoin (fun o => next (trec o)))
    end.

  Definition trec (o: Ord.t): D.
    eapply Ord.rec.
    { eapply base. }
    { eapply next. }
    2: { eapply o. }
    i. eapply djoin.
    instantiate (1:=@Ord.build A ds).
  Defined.
End TREC.
Ord.orec : Ord.t -> (Ord.t -> Ord.t) -> Ord.t -> Ord.t
Ord.rec : forall [D : Type], D -> (D -> D) -> (forall A : Type, (A -> D) -> D) -> Ord.t -> D


Module THEORY2. Section THEORY.
  Variable T0 : Type.
  Variable T1 : forall (x0: @T0), Type.

  Local Notation rel := (rel2 T0 T1).

  Variable gf: rel -> rel.
  Hypothesis gf_mon: monotone2 gf.

  Definition forall2 (A: Type) (P: A -> rel): rel := fun x0 x1 => forall (a: A), P a x0 x1.
  (* Notation forall2 := (fun (A: Type) (P: A -> rel) x0 x1 => forall (a: A), P a x0 x1). *)
  Notation "'forall2' x .. y , p" := (forall2 (fun x => .. (forall2 (fun y => p)) ..))
                                      (at level 200, x binder, right associativity,
                                        format "'[' 'forall2'  '/  ' x  ..  y ,  '/  ' p ']'").
  (* Notation "'forall2' a , P" := (forall2 (fun a => P)) (at level 50). *)

  Definition seq: Ord.t -> rel.
    eapply Ord.rec.
    { r. eapply top2. }
    { eapply gf. }
    { i. r. eapply (forall2 a, ds a). }
  Defined.

  Definition cpn_kleene (r: rel) : rel := forall2 o (LE: r <2= seq o), seq o.

  Theorem cpn_kleene_cpn: cpn2 gf = cpn_kleene.
  Proof.
    extensionality r.
    extensionality _x0.
    extensionality _x1.
    eapply prop_ext. split; i.
    - r. ii.
      move a at top. revert_until gf_mon.
      pattern a.
      eapply ClassicOrd.ind.
      + ii. r.
        eapply Ord.rec_is_O in ZERO; eauto.
        rewrite Ord.rec_red.
  Qed.

End THEORY. End THEORY2.
