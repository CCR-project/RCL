Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import Any.
Require Import SimModSem.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.

Set Implicit Arguments.

#[export] Hint Resolve sim_itree_mon: paco.
#[export] Hint Resolve cpn8_wcompat: paco.


Ltac ired_l := try (prw _red_gen 2 1 0).
Ltac ired_r := try (prw _red_gen 1 1 0).

Ltac ired_both := ired_l; ired_r.



(* "safe" simulation constructors *)
Section SIM.

  Let st_local: Type := (Any.t).

  Variable mt: alist string (Any.t -> itree Es Any.t).

  Variable world: Type.

  Let W: Type := (Any.t) * (Any.t).
  Variable wf: world -> W -> Prop.
  Variable le: relation world.

  Inductive _safe_sim_itree
            (r g: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
            {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | safe_sim_itree_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))

  | safe_sim_itree_call
      i_src0 i_tgt0 w w0 st_src0 st_tgt0
      fn varg k_src k_tgt
      (WF: wf w0 (st_src0, st_tgt0))
      (K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
          g _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret))
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                    (st_tgt0, trigger (Call fn varg) >>= k_tgt)
  | safe_sim_itree_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          g _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                    (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | safe_sim_itree_call_tgt
      i_src0 i_tgt0 w st_src0 st_tgt0
      fn ft varg i_src k_tgt
      (FINDT: In (fn, ft) mt)
      (K: r _ _ RR i_src0 true w (st_src0, i_src) (st_tgt0, ft varg >>= k_tgt))
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w (st_src0, i_src)
                    (st_tgt0, trigger (Call fn varg) >>= k_tgt)

  | safe_sim_itree_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: r _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)
  | safe_sim_itree_choose_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: exists (x: X), r _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Choose X) >>= k_src)
                    (st_tgt0, i_tgt)
  | safe_sim_itree_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), r _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                    (st_tgt0, i_tgt)

  | safe_sim_itree_pput_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      st_src1
      (K: r _ _ RR true i_tgt0 w0 (st_src1, k_src tt) (st_tgt0, i_tgt))
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, trigger (PPut st_src1) >>= k_src)
                    (st_tgt0, i_tgt)

  | safe_sim_itree_pget_src
      i_src0 i_tgt0 w0 st_tgt0 st_src0
      k_src i_tgt
      (K: r _ _ RR true i_tgt0 w0 (st_src0, k_src st_src0) (st_tgt0, i_tgt))
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, trigger (PGet) >>= k_src)
                    (st_tgt0, i_tgt)


  | safe_sim_itree_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | safe_sim_itree_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                    (st_tgt0, trigger (Choose X) >>= k_tgt)
  | safe_sim_itree_take_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: exists (x: X), r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                    (st_tgt0, trigger (Take X) >>= k_tgt)

  | safe_sim_itree_pput_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      st_tgt1
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt1, k_tgt tt))
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                    (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)

  | safe_sim_itree_pget_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      k_tgt i_src
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt st_tgt0))
    :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                    (st_tgt0, trigger (PGet) >>= k_tgt)
  .

  Lemma safe_sim_sim r g:
    @_safe_sim_itree (gpaco8 (_sim_itree mt wf le) (cpn8 (_sim_itree mt wf le)) r g) (gpaco8 (_sim_itree mt wf le) (cpn8 (_sim_itree mt wf le)) g g)
    <8=
    gpaco8 (_sim_itree mt wf le) (cpn8 (_sim_itree mt wf le)) r g.
  Proof.
    i. eapply sim_itreeC_spec. inv PR; try by (econs; eauto).
  Qed.

End SIM.


Ltac prep := ired_both.

Ltac _force_l :=
  prep;
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, unleftN ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unleftN ox) as tvar eqn:thyp; unfold unleftN in thyp; subst tvar;
    let name := fresh "_UNLEFTN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, unrightN ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unrightN ox) as tvar eqn:thyp; unfold unrightN in thyp; subst tvar;
    let name := fresh "_UNRIGHTN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, guarantee ?P >>= _) (_, _)) ] =>
      (* let tvar := fresh "tmp" in *)
      (* let thyp := fresh "TMP" in *)
      (* remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar; *)
      (* let name := fresh "_GUARANTEE" in *)
      (* destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_src; [exists name]|contradict name]; cycle 1 *)
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
      let name := fresh "_GUARANTEE" in
      destruct (excluded_middle_informative P) as [name|name]; [| unfold triggerNB; ired_l]; cycle 1

  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, ITree.bind (interp _ guarantee ?P) _ (_, _))) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_src; [exists name]|contradict name]; cycle 1

   (* TODO: handle interp_hCallE_tgt better and remove this case *)
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, ITree.bind (interp _ (guarantee ?P )) _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_src; [exists name]|contradict name]; cycle 1; clear name

  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_tgt; apply sim_itreeC_spec; econs; unseal i_tgt
  end
.

Ltac _force_r :=
  prep;
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unleftU ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unleftU ox) as tvar eqn:thyp; unfold unleftU in thyp; subst tvar;
    let name := fresh "_UNLEFTU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unrightU ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unrightU ox) as tvar eqn:thyp; unfold unrightU in thyp; subst tvar;
    let name := fresh "_UNRIGHTU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
      (* let tvar := fresh "tmp" in *)
      (* let thyp := fresh "TMP" in *)
      (* remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar; *)
      (* let name := fresh "_ASSUME" in *)
      (* destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_take_tgt; [exists name]|contradict name]; cycle 1 *)
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
      let name := fresh "_ASSUME" in
      destruct (excluded_middle_informative P) as [name|name]; [| unfold triggerUB; ired_r]; cycle 1

  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_src; apply sim_itreeC_spec; econs; unseal i_src
  end
.

Ltac _step :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, triggerUB >>= _) (_, _)) ] =>
    unfold triggerUB; ired_l; _step; done
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_both; _force_l; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, unleftU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unleftU ox) as tvar eqn:thyp; unfold unleftU in thyp; subst tvar;
    let name := fresh "_UNLEFTU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_both; _force_l; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, unrightU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unrightU ox) as tvar eqn:thyp; unfold unrightU in thyp; subst tvar;
    let name := fresh "_UNRIGHTU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_both; _force_l; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    (* let tvar := fresh "tmp" in *)
    (* let thyp := fresh "TMP" in *)
    (* remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar; *)
    (* let name := fresh "_ASSUME" in *)
    (* ired_both; apply sim_itreeC_spec; eapply sim_itreeC_take_src; intro name *)
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
      let name := fresh "_ASSUME" in
      destruct (excluded_middle_informative P) as [name|name]; [| unfold triggerUB; ired_l]; cycle 1

  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, triggerNB >>= _) (_, _)) ] =>
    unfold triggerNB; ired_r; _step; done
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_both; _force_r; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unleftN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unleftN ox) as tvar eqn:thyp; unfold unleftN in thyp; subst tvar;
    let name := fresh "_UNLEFTN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_both; _force_r; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unrightN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unrightN ox) as tvar eqn:thyp; unfold unrightN in thyp; subst tvar;
    let name := fresh "_UNRIGHTN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_both; _force_r; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    (* let tvar := fresh "tmp" in *)
    (* let thyp := fresh "TMP" in *)
    (* remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar; *)
    (* let name := fresh "_GUARANTEE" in *)
    (* ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_tgt; intro name *)
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
      let name := fresh "_GUARANTEE" in
      destruct (excluded_middle_informative P) as [name|name]; [| unfold triggerNB; ired_r]; cycle 1



  | _ => (*** default ***)
    eapply safe_sim_sim; econs; i
  end;
  match goal with
  | [ |- exists (_: unit), _ ] => esplits; [eauto|..]; i
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.
Ltac _steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) simpl).

Ltac steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) simpl; des_ifs_safe).
Ltac force_l := _force_l.
Ltac force_r := _force_r.

(* Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 '------------------------------------------------------------------' src2 tgt2" *)
(*   := *)
(*     (gpaco8 (_sim_itree _ wf _) _ _ _ _ _ _ _ _ n ((Any.pair src0 src1), src2) (tgt0, tgt2)) *)
(*       (at level 60, *)
(*        format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' "). *)

(* Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' '------------------------------------------------------------------' src2 tgt2" *)
(*   := *)
(*     (gpaco8 (_sim_itree _ wf _) _ _ _ _ _ _ _ _ n (src0, src2) (tgt0, tgt2)) *)
(*       (at level 60, *)
(*        format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' "). *)

(* Section TEST. *)
(*   Context `{Σ: GRA.t}. *)
(*   Let wf := (mk_wf (fun (_ : unit) (_ _ : Any.t) => bi_pure True)). *)
(*   Let le := fun (_ _: unit) => True. *)
(*   Variable (srcs0 tgts0: Any.t). *)

(*   Goal gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) bot8 bot8 Any.t Any.t (fun _ _ => eq) false false tt *)
(*        (srcs0, triggerUB >>= idK) (tgts0, triggerUB >>= idK). *)
(*   Proof. *)
(*     steps. *)
(*   Qed. *)

(*   Goal gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) bot8 bot8 Any.t Any.t (fun _ _ => eq) false false tt *)
(*        (srcs0, triggerNB >>= idK) (tgts0, triggerNB >>= idK). *)
(*   Proof. *)
(*     steps. *)
(*   Qed. *)

(* End TEST. *)


(* Ltac astep_full _fn _args _next _n1 := *)
(*   eapply (@APC_step_clo _ _fn _args _next _n1); *)
(*   [(try by ((try stb_tac); refl))| *)
(*    oauto| *)
(*   ]. *)

(* Ltac astep _fn _args := *)
(*   eapply (@APC_step_clo _ _fn _args); *)
(*   [(try by ((try stb_tac); refl))| *)
(*    oauto| *)
(*   ]. *)

(* Ltac acatch := *)
(*   match goal with *)
(*   | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn ?args) >>= _)) ] => *)
(*     astep fn args *)
(*   end. *)

(* Ltac astart _at_most := *)
(*   eapply (@APC_start_clo _ _at_most) *)
(* . *)

(* Ltac astop := *)
(*   match goal with *)
(*   | [ |- (gpaco8 (_sim_itree _ _) _ _ _ _ _ _ _ _ _ (_, interp_hCallE_tgt _ _ _ APC _ >>= _) (_, _)) ] => astart 0 *)
(*   | _ => idtac *)
(*   end; *)
(*   eapply APC_stop_clo. *)

Ltac init :=
  let varg_src := fresh "varg_src" in
  let mn := fresh "mn" in
  let varg := fresh "varg" in
  let EQ := fresh "EQ" in
  let w := fresh "w" in
  let mrp_src := fresh "mrp_src" in
  let mp_tgt := fresh "mp_tgt" in
  let WF := fresh "WF" in
  split; ss; intros varg_src [mn varg] EQ w mrp_src mp_tgt WF;
  try subst varg_src; cbn; ginit;
  match goal with
  (* | |- gpaco8 _ _ _ _ _ _ _ _ _ _ (_, KModSem.disclose_ksb_tgt _ _ (ksb_trivial _) _) _ => *)
  (*   eapply trivial_init_clo; *)
  (*   try (unfold fun_to_tgt, cfunN, cfunU, KModSem.disclose_ksb_tgt, fun_to_tgt); *)
  (*   rewrite HoareFun_parse; simpl *)
  (* | |- gpaco8 _ _ _ _ _ _ _ _ _ _ (_, KModSem.disclose_ksb_tgt _ _ _ _) _ => *)
  (*   try (unfold fun_to_tgt, cfunN, cfunU, KModSem.disclose_ksb_tgt, fun_to_tgt); *)
  (*   simpl; *)
  (*   apply sim_itreeC_spec; apply sim_itreeC_take_src; intros [];rewrite HoareFun_parse; simpl *)
  | |- _ =>
    try (unfold cfunN, cfunU); simpl
    (* try (unfold fun_to_tgt, cfunN, cfunU; rewrite HoareFun_parse); simpl *)
  end.

(* Ltac harg := *)
(*   let PRE := constr:("PRE") in *)
(*   let INV := constr:("INV") in *)
(*   eapply (@harg_clo _ _ PRE INV); *)
(*   [eassumption *)
(*   | *)
(*   ]; i. *)

(* Tactic Notation "hret" uconstr(a) := *)
(*   eapply (@hret_clo _ _ a); unshelve_goal; *)
(*   [eassumption *)
(*   | *)
(*   |start_ipm_proof *)
(*   |try by (i; (try unfold lift_rel); esplits; et) *)
(*   ]. *)

(* Tactic Notation "hcall" uconstr(x) uconstr(a) "with" constr(Hns) := *)
(*   let POST := get_fresh_name_tac "POST" in *)
(*   let INV := get_fresh_name_tac "INV" in *)
(*   let Hns := select_ihyps Hns in *)
(*   eapply (@hcall_clo _ Hns POST INV _ x _ a); *)
(*   unshelve_goal; *)
(*   [eassumption *)
(*   |start_ipm_proof *)
(*   | *)
(*   |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H) *)
(*   ]. *)

(* Tactic Notation "hcall_weaken" uconstr(fsp) uconstr(x) uconstr(a) "with" constr(Hns) := *)
(*   let POST := get_fresh_name_tac "POST" in *)
(*   let INV := get_fresh_name_tac "INV" in *)
(*   let Hns := select_ihyps Hns in *)
(*   eapply (@hcall_clo_weaken _ Hns POST INV fsp x _ a); *)
(*   unshelve_goal; *)
(*   [ *)
(*   |eassumption *)
(*   |start_ipm_proof *)
(*   | *)
(*   |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H) *)
(*   ]. *)

(* Ltac iarg := *)
(*   let PRE := constr:("PRE") in *)
(*   let INV := constr:("INV") in *)
(*   let CLOSED := constr:("☃CLOSED") in *)
(*   eapply (@harg_clo _ _ PRE INV); *)
(*   [eassumption *)
(*   | *)
(*   ]; *)
(*   i; *)
(*   mDesSep PRE as CLOSED PRE; *)
(*   match goal with *)
(*   | [ |- (gpaco8 _ _ _ _ _ _ _ _ _ ?w _ _)] => *)
(*     destruct w as [?|[?mp_src ?mp_tgt]]; simpl; *)
(*     [ *)
(*         |mAssertPure False; ss; iDestruct "INV" as "[INV _]"; iApply (inv_closed_unique with "☃CLOSED INV") *)
(*     ] *)
(*   end. *)

(* Tactic Notation "icall_open" uconstr(x) "with" constr(Hns) := *)
(*   let POST := get_fresh_name_tac "POST" in *)
(*   let INV := constr:("☃CLOSED") in *)
(*   let Hns := select_ihyps Hns in *)
(*   let Hns := constr:("☃CLOSED"::Hns) in *)
(*   eapply (@hcall_clo _ Hns POST INV _ x _ (inr (_, _))); *)
(*   unshelve_goal; *)
(*   [eassumption *)
(*   |start_ipm_proof; iSplitL "☃CLOSED"; [iModIntro; iSplitL "☃CLOSED"; [iExact "☃CLOSED"|ss]|] *)
(*   | *)
(*   | *)
(*   on_current ltac:(fun H => try clear H); *)
(*   intros ? ? ? ? [|[?mp_src ?mp_tgt]]; i; simpl; *)
(*   on_current ltac:(fun H => simpl in H); *)
(*   [exfalso; match goal with | H: inv_le _ _ _ |- _ => cbn in H; inv H end *)
(*   |mDesSep "☃CLOSED" as "☃CLOSED" "☃TMP"; mPure "☃TMP" as [[] []] *)
(*   ] *)
(*   ]. *)

(* Tactic Notation "icall_weaken" uconstr(ftsp) uconstr(x) uconstr(a) "with" constr(Hns) := *)
(*   let POST := get_fresh_name_tac "POST" in *)
(*   let INV := get_fresh_name_tac "INV" in *)
(*   let CLOSED := constr:("☃CLOSED") in *)
(*   let TMP := constr:("☃TMP") in *)
(*   let Hns := select_ihyps Hns in *)
(*   let Hns := constr:("☃CLOSED"::Hns) in *)
(*   eapply (@hcall_clo_weaken _ Hns POST INV ftsp x _ (inl a)); *)
(*   unshelve_goal; *)
(*   [|eassumption *)
(*    |start_ipm_proof; iFrame "☃CLOSED" *)
(*    | *)
(*    |on_current ltac:(fun H => try clear H); *)
(*     intros ? ? ? ? [|[?mp_src ?mp_tgt]]; i; simpl; *)
(*     on_current ltac:(fun H => simpl in H); *)
(*     [ *)
(*       mDesSep POST as "☃CLOSED" POST *)
(*     | *)
(*     mDesSep INV as "☃CLOSED" INV; *)
(*     mDesSep POST as "☃TMP" POST; *)
(*     mAssertPure False; [iApply (inv_closed_unique with "☃TMP ☃CLOSED")|ss] *)
(*     ] *)
(*   ]. *)

(* Tactic Notation "iret" uconstr(a) := *)
(*   eapply (@hret_clo _ _ (inl a)); unshelve_goal; *)
(*   [eassumption *)
(*   | *)
(*   |start_ipm_proof; iFrame "☃CLOSED" *)
(*   |try by (i; (try unfold lift_rel); esplits; et) *)
(*   ]. *)


Global Opaque interp.
(* Global Opaque _APC APC interp interp_hCallE_tgt. *)

(* Global Opaque HoareFun HoareFunArg HoareFunRet HoareCall. *)

Definition __hide_mark A (a : A) : A := a.
Lemma intro_hide_mark: forall A (a: A), a = __hide_mark a. refl. Qed.

Ltac hide_k :=
  match goal with
  | [ |- (gpaco8 _ _ _ _ _ _ _ _ _ _ (_, ?isrc >>= ?ksrc) (_, ?itgt >>= ?ktgt)) ] =>
    erewrite intro_hide_mark with (a:=ksrc);
    erewrite intro_hide_mark with (a:=ktgt);
    let name0 := fresh "__KSRC__" in set (__hide_mark ksrc) as name0; move name0 at top;
    let name0 := fresh "__KTGT__" in set (__hide_mark ktgt) as name0; move name0 at top
  end.

Ltac unhide_k :=
  do 2 match goal with
  | [ H := __hide_mark _ |- _ ] => subst H
  end;
  rewrite <- ! intro_hide_mark
.

Ltac deflag :=
  match goal with
  | [ |- (gpaco8 _ _ _ _ _ _ _ true true _ _ _) ] =>
    eapply sim_itree_progress_flag
  | [ |- (gpaco8 _ _ _ _ _ _ _ _ _ _ _ _) ] =>
    eapply sim_itree_flag_down
  | _ => fail
  end.

Ltac ired_eq_l := (Red.prw IRed._red_gen 2 0).
Ltac ired_eq_r := (Red.prw IRed._red_gen 1 0).

Ltac unfold_goal H :=
  match goal with
  | [|- gpaco8 (_sim_itree ?_temp1 _ _) (cpn8 (_sim_itree ?_temp2 _ _)) _ _ _ _ _ _ _ _ _ _] =>
      let tvar1 := fresh "temp1" in
      let tvar2 := fresh "temp2" in
      remember _temp1 as tvar1; remember _temp2 as tvar2; unfold H; subst tvar1 tvar2
  end.

Ltac hide_src :=
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, _)) ] =>
      let hsrc := fresh "hide_src" in set i_src as hsrc at 1
  end.

Ltac hide_tgt :=
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, ?i_tgt)) ] =>
      let htgt := fresh "hide_tgt" in set i_tgt as htgt at 2
  end.
