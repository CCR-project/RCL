From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.

Set Implicit Arguments.

(* ========================================================================== *)
(** ** Rewriting Leamms *)
Section PROOFS.

  Context `{Σ: GRA.t}.

  (* expr *)
  Lemma denote_expr_Var
        ge le0 v
    :
      interp_imp ge (denote_expr (Var v)) le0 =
      interp_imp ge (u <- trigger (GetVar v);; assume (wf_val u);; Ret u) le0.
  Proof. reflexivity. Qed.

  Lemma denote_expr_Lit
        ge le0 n
    :
      interp_imp ge (denote_expr (Lit n)) le0 =
      interp_imp ge (assume (wf_val n);; Ret n) le0.
  Proof. reflexivity. Qed.

  Lemma denote_expr_Plus
        ge le0 a b
    :
      interp_imp ge (denote_expr (Plus a b)) le0 =
      interp_imp ge (l <- denote_expr a;; r <- denote_expr b;; u <- unwrapU (vadd l r);; assume (wf_val u);; Ret u) le0.
  Proof. reflexivity. Qed.

  Lemma denote_expr_Minus
        ge le0 a b
    :
      interp_imp ge (denote_expr (Minus a b)) le0 =
      interp_imp ge (l <- denote_expr a;; r <- denote_expr b;; u <- unwrapU (vsub l r);; assume (wf_val u);; Ret u) le0.
  Proof. reflexivity. Qed.

  Lemma denote_expr_Mult
        ge le0 a b
    :
      interp_imp ge (denote_expr (Mult a b)) le0 =
      interp_imp ge (l <- denote_expr a;; r <- denote_expr b;; u <- unwrapU (vmul l r);; assume (wf_val u);; Ret u) le0.
  Proof. reflexivity. Qed.

  (* stmt *)

  Lemma denote_stmt_Skip
        ge le0
    :
      interp_imp ge (denote_stmt (Skip)) le0 =
      interp_imp ge (Ret Vundef) le0.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Assign
        ge le0 x e
    :
      interp_imp ge (denote_stmt (Assign x e)) le0 =
      interp_imp ge (v <- denote_expr e ;; trigger (SetVar x v) ;; Ret Vundef) le0.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Seq
        ge le0 a b
    :
      interp_imp ge (denote_stmt (Seq a b)) le0 =
      interp_imp ge (denote_stmt a ;; denote_stmt b) le0.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_If
        ge le0 i t e
    :
      interp_imp ge (denote_stmt (If i t e)) le0 =
      interp_imp ge (v <- denote_expr i ;; `b: bool <- (is_true v)? ;;
      if b then (denote_stmt t) else (denote_stmt e)) le0.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_AddrOf
        ge le0 x X
    :
      interp_imp ge (denote_stmt (AddrOf x X)) le0 =
      interp_imp ge (v <- trigger (GetPtr X);; trigger (SetVar x v);; Ret Vundef) le0.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Malloc
        ge le0 x se
    :
      interp_imp ge (denote_stmt (Malloc x se)) le0 =
      interp_imp ge (s <- denote_expr se;;
      v <- trigger (Call "alloc" ([s]↑));; v <- unwrapN(v↓);;
      trigger (SetVar x v);; Ret Vundef) le0.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Free
        ge le0 pe
    :
      interp_imp ge (denote_stmt (Free pe)) le0 =
      interp_imp ge (p <- denote_expr pe;;
      trigger (Call "free" ([p]↑));; Ret Vundef) le0.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Load
        ge le0 x pe
    :
      interp_imp ge (denote_stmt (Load x pe)) le0 =
      interp_imp ge (p <- denote_expr pe;;
      v <- trigger (Call "load" ([p]↑));; v <- unwrapN(v↓);;
      trigger (SetVar x v);; Ret Vundef) le0.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Store
        ge le0 pe ve
    :
      interp_imp ge (denote_stmt (Store pe ve)) le0 =
      interp_imp ge (p <- denote_expr pe;; v <- denote_expr ve;;
      trigger (Call "store" ([p ; v]↑));; Ret Vundef) le0.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_Cmp
        ge le0 x ae be
    :
      interp_imp ge (denote_stmt (Cmp x ae be)) le0 =
      interp_imp ge ( a <- denote_expr ae;; b <- denote_expr be;;
      v <- trigger (Call "cmp" ([a ; b]↑));; v <- unwrapN (v↓);;
      trigger (SetVar x v);; Ret Vundef) le0.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallFun
        ge le0 x f args
    :
      interp_imp ge (denote_stmt (CallFun x f args)) le0 =
      interp_imp ge (
      if (call_mem f)
      then triggerUB
      else
        eval_args <- (denote_exprs args);;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef) le0.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallPtr
        ge le0 x e args
    :
      interp_imp ge (denote_stmt (CallPtr x e args)) le0 =
      interp_imp ge (
      p <- denote_expr e;; f <- trigger (GetName p);;
      if (call_mem f)
      then triggerUB
      else
        eval_args <- (denote_exprs args);;
        v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
        trigger (SetVar x v);; Ret Vundef) le0.
  Proof. reflexivity. Qed.

  Lemma denote_stmt_CallSys
        ge le0 x f args
    :
      interp_imp ge (denote_stmt (CallSys x f args)) le0 =
      interp_imp ge (
      eval_args <- (denote_exprs args);;
      v <- trigger (Syscall f eval_args top1);;
      trigger (SetVar x v);; Ret Vundef) le0.
  Proof. reflexivity. Qed.

  (* interp_imp *)

  Lemma interp_imp_bind
        T R (itr: itree _ T) (ktr: T -> itree _ R) ge le0
    :
      interp_imp ge (v <- itr ;; ktr v) le0 =
      '(le1, v) <- interp_imp ge itr le0;;
      interp_imp ge (ktr v) le1.
  Proof.
    unfold interp_imp. unfold interp_GlobEnv.
    unfold interp_ImpState. grind. des_ifs.
  Qed.

  Lemma interp_imp_tau
        T (itr: itree _ T) ge le0
    :
      interp_imp ge (tau;; itr) le0 =
      tau;; interp_imp ge itr le0.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    grind.
  Qed.

  Lemma interp_imp_Ret
        T ge le0 (v: T)
    :
      interp_imp ge (Ret v) le0 = Ret (le0, v).
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    grind.
  Qed.

  Lemma interp_imp_triggerUB
        T ge le0
    :
      (interp_imp ge (triggerUB) le0 : itree _ (lenv *T)) = triggerUB.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, pure_state, triggerUB.
    grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_triggerUB_bind
        U T ge le0 (ktr: U -> itree _ T)
    :
      (interp_imp ge (x <- triggerUB;; ktr x) le0 : itree _ (lenv *T)) = triggerUB.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, pure_state, triggerUB.
    grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_triggerNB
        T ge le0
    :
      (interp_imp ge (triggerNB) le0 : itree _ (lenv * T)) = triggerNB.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, pure_state, triggerNB.
    grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_triggerNB_bind
        U T ge le0 (ktr: U -> itree _ T)
    :
      (interp_imp ge (x <- triggerNB;; ktr x) le0 : itree _ (lenv * T)) = triggerNB.
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv, pure_state, triggerNB.
    grind. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_unwrapU
        T x ge le0
    :
      (interp_imp ge (unwrapU x) le0 : itree _ (lenv * T)) =
      x <- unwrapU x;; Ret (le0, x).
  Proof.
    unfold unwrapU. des_ifs.
    - rewrite interp_imp_Ret. ired. ss.
    - rewrite interp_imp_triggerUB.
      unfold triggerUB. grind.
  Qed.

  Lemma interp_imp_unwrapN
        T x ge le0
    :
      (interp_imp ge (unwrapN x) le0 : itree _ (lenv * T)) =
      x <- unwrapN x;; Ret (le0, x).
  Proof.
    unfold unwrapN. des_ifs.
    - rewrite interp_imp_Ret. ired. ss.
    - rewrite interp_imp_triggerNB.
      unfold triggerNB. grind.
  Qed.

  Lemma interp_imp_GetPtr
        ge le0 X
    :
      interp_imp ge (trigger (GetPtr X)) le0 =
      r <- (ge.(SkEnv.id2blk) X)? ;; tau;; Ret (le0, Vptr r 0).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState, unwrapU.
    des_ifs; grind.
    - rewrite interp_trigger. grind.
      unfold unwrapU. des_ifs. grind.
    - rewrite interp_trigger. grind.
      unfold unwrapU. des_ifs. unfold triggerUB, pure_state. grind.
  Qed.

  Lemma interp_imp_GetName
        ge le0 x
    :
      interp_imp ge (trigger (GetName x)) le0 =
      match x with
      | Vptr n 0 => u <- unwrapU (SkEnv.blk2id ge n);; tau;; Ret (le0, u)
      | _ => triggerUB
      end
  .
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState.
    destruct x; try destruct ofs.
    1,3,4,5:(rewrite interp_trigger; grind; unfold triggerUB, pure_state; grind).
    rewrite interp_trigger. grind. unfold unwrapU.
    destruct (SkEnv.blk2id ge blk).
    2:{ unfold triggerUB, pure_state. grind. }
    grind.
  Qed.

  Lemma interp_imp_GetVar
        ge le0 x
    :
      (interp_imp ge (trigger (GetVar x)) le0 : itree Es _) =
      r <- unwrapU (alist_find x le0);; tau;; tau;; Ret (le0, r).
  Proof.
    unfold interp_imp, interp_ImpState, interp_GlobEnv.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_SetVar
        ge le0 x v
    :
      interp_imp ge (trigger (SetVar x v)) le0 =
      tau;; tau;; Ret (alist_add x v le0, ()).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState.
    rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_Call
        ge le0 f args
    :
      interp_imp ge (trigger (Call f args)) le0 =
      v <- trigger (Call f args);; tau;; tau;; Ret (le0, v).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState.
    unfold pure_state. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_Syscall
        ge le0 f args t
    :
      interp_imp ge (trigger (Syscall f args t)) le0 =
      v <- trigger (Syscall f args t);; tau;; tau;; Ret (le0, v).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState.
    unfold pure_state. rewrite interp_trigger. grind.
  Qed.

  Lemma interp_imp_assume
        ge le0 p
    :
      interp_imp ge (assume p) le0 = assume p;; tau;; tau;; Ret (le0, ()).
  Proof.
    unfold interp_imp, interp_GlobEnv, interp_ImpState.
    unfold assume. grind. rewrite interp_trigger. grind.
    unfold pure_state. grind.
  Qed.

  Lemma interp_imp_expr_Var
        ge le0 v
    :
      interp_imp ge (denote_expr (Var v)) le0 =
      r <- unwrapU (alist_find v le0);; tau;; tau;; assume (wf_val r);; tau;; tau;; Ret (le0, r).
  Proof.
    rewrite denote_expr_Var. rewrite interp_imp_bind. rewrite interp_imp_GetVar.
    grind. rewrite interp_imp_bind. rewrite interp_imp_assume. grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_expr_Lit
        ge le0 n
    :
      interp_imp ge (denote_expr (Lit n)) le0 =
      assume (wf_val n);; tau;; tau;; Ret (le0, n).
  Proof.
    rewrite denote_expr_Lit. rewrite interp_imp_bind. rewrite interp_imp_assume. grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_expr_Plus
        ge le0 a b
    :
      interp_imp ge (denote_expr (Plus a b)) le0 =
      '(le1, l) <- interp_imp ge (denote_expr a) le0 ;;
      '(le2, r) <- interp_imp ge (denote_expr b) le1 ;;
      v <- (vadd l r)? ;;
      assume (wf_val v);;; tau;; tau;;
      Ret (le2, v)
  .
  Proof.
    rewrite denote_expr_Plus. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_unwrapU. grind.
    rewrite interp_imp_bind. rewrite interp_imp_assume. grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_expr_Minus
        ge le0 a b
    :
      interp_imp ge (denote_expr (Minus a b)) le0 =
      '(le1, l) <- interp_imp ge (denote_expr a) le0 ;;
      '(le2, r) <- interp_imp ge (denote_expr b) le1 ;;
      v <- (vsub l r)? ;;
      assume (wf_val v);;; tau;; tau;;
      Ret (le2, v)
  .
  Proof.
    rewrite denote_expr_Minus. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_unwrapU. grind.
    rewrite interp_imp_bind. rewrite interp_imp_assume. grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_expr_Mult
        ge le0 a b
    :
      interp_imp ge (denote_expr (Mult a b)) le0 =
      '(le1, l) <- interp_imp ge (denote_expr a) le0 ;;
      '(le2, r) <- interp_imp ge (denote_expr b) le1 ;;
      v <- (vmul l r)? ;;
      assume (wf_val v);;; tau;; tau;;
      Ret (le2, v)
  .
  Proof.
    rewrite denote_expr_Mult. rewrite interp_imp_bind.
    grind. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_unwrapU. grind.
    rewrite interp_imp_bind. rewrite interp_imp_assume. grind. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Skip
        ge le0
    :
      interp_imp ge (denote_stmt (Skip)) le0 =
      Ret (le0, Vundef).
  Proof.
    rewrite denote_stmt_Skip. apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Assign
        ge le0 x e
    :
      interp_imp ge (denote_stmt (Assign x e)) le0 =
      '(le1, v) <- interp_imp ge (denote_expr e) le0 ;;
      tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof.
    rewrite denote_stmt_Assign.
    rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Seq
        ge le0 a b
    :
      interp_imp ge (denote_stmt (Seq a b)) le0 =
      '(le1, _) <- interp_imp ge (denote_stmt a) le0 ;;
      interp_imp ge (denote_stmt b) le1.
  Proof.
    rewrite denote_stmt_Seq. apply interp_imp_bind.
  Qed.

  Lemma interp_imp_If
        ge le0 i t e
    :
      interp_imp ge (denote_stmt (If i t e)) le0 =
      '(le1, v) <- interp_imp ge (denote_expr i) le0 ;;
      `b: bool <- (is_true v)? ;;
       if b
       then interp_imp ge (denote_stmt t) le1
       else interp_imp ge (denote_stmt e) le1.
  Proof.
    rewrite denote_stmt_If. rewrite interp_imp_bind. grind.
    destruct (is_true v); grind; des_ifs.
    rewrite interp_imp_triggerUB_bind.
    unfold triggerUB. grind.
  Qed.

  Lemma interp_imp_AddrOf
        ge le0 x X
    :
      interp_imp ge (denote_stmt (AddrOf x X)) le0 =
      r <- (ge.(SkEnv.id2blk) X)? ;; tau;;
      tau;; tau;; Ret (alist_add x (Vptr r 0) le0, Vundef).
  Proof.
    rewrite denote_stmt_AddrOf. rewrite interp_imp_bind.
    rewrite interp_imp_GetPtr. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Malloc
        ge le0 x se
    :
      interp_imp ge (denote_stmt (Malloc x se)) le0 =
      '(le1, s) <- interp_imp ge (denote_expr se) le0;;
      v <- trigger (Call "alloc" ([s]↑));;
      tau;; tau;; v <- unwrapN (v↓);;
      tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof.
    rewrite denote_stmt_Malloc. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_Call. grind.
    rewrite interp_imp_bind. rewrite interp_imp_unwrapN. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Free
        ge le0 pe
    :
      interp_imp ge (denote_stmt (Free pe)) le0 =
      '(le1, p) <- interp_imp ge (denote_expr pe) le0;;
      trigger (Call "free" ([p]↑));; tau;; tau;; Ret (le1, Vundef).
  Proof.
    rewrite denote_stmt_Free. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_Call. grind.
    apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Load
        ge le0 x pe
    :
      interp_imp ge (denote_stmt (Load x pe)) le0 =
      '(le1, p) <- interp_imp ge (denote_expr pe) le0;;
      v <- trigger (Call "load" ([p]↑));;
      tau;; tau;; v <- unwrapN (v↓);;
      tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof.
    rewrite denote_stmt_Load. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_Call. grind.
    rewrite interp_imp_bind. rewrite interp_imp_unwrapN. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Store
        ge le0 pe ve
    :
      interp_imp ge (denote_stmt (Store pe ve)) le0 =
      '(le1, p) <- interp_imp ge (denote_expr pe) le0;;
      '(le2, v) <- interp_imp ge (denote_expr ve) le1;;
      trigger (Call "store" ([p ; v]↑));; tau;; tau;; Ret (le2, Vundef).
  Proof.
    rewrite denote_stmt_Store. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_Call. grind.
    apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Cmp
        ge le0 x ae be
    :
      interp_imp ge (denote_stmt (Cmp x ae be)) le0 =
      '(le1, a) <- interp_imp ge (denote_expr ae) le0;;
      '(le2, b) <- interp_imp ge (denote_expr be) le1;;
      v <- trigger (Call "cmp" ([a ; b]↑));;
      tau;; tau;; v <- unwrapN (v↓);;
      tau;; tau;; Ret (alist_add x v le2, Vundef).
  Proof.
    rewrite denote_stmt_Cmp. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_Call. grind.
    rewrite interp_imp_bind. rewrite interp_imp_unwrapN. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_Call_args
        ge le0 x f args
    :
      interp_imp ge (
                   eval_args <- (denote_exprs args);;
                   v <- trigger (Call f (eval_args↑));; v <- unwrapN (v↓);;
                   trigger (SetVar x v);; Ret Vundef) le0
      =
      '(le1, vals) <- interp_imp ge (denote_exprs args) le0;;
      v <- trigger (Call f (vals↑));;
      tau;; tau;; v <- unwrapN (v↓);;
      tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof.
    rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_Call. grind.
    rewrite interp_imp_bind. rewrite interp_imp_unwrapN. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_CallFun
        ge le0 x f args
    :
      interp_imp ge (denote_stmt (CallFun x f args)) le0 =
      if (call_mem f)
      then triggerUB
      else
        '(le1, vals) <- interp_imp ge (denote_exprs args) le0;;
        v <- trigger (Call f (vals↑));;
        tau;; tau;; v <- unwrapN (v↓);;
        tau;; tau;; Ret (alist_add x v le1, Vundef).
  Proof.
    rewrite denote_stmt_CallFun. des_ifs; try (apply interp_imp_Call_args).
    apply interp_imp_triggerUB.
  Qed.

  Lemma interp_imp_CallPtr
        ge le0 x e args
    :
      interp_imp ge (denote_stmt (CallPtr x e args)) le0 =
      '(le1, p) <- interp_imp ge (denote_expr e) le0;;
      match p with
      | Vptr n 0 =>
        match (SkEnv.blk2id ge n) with
        | Some f =>
          if (call_mem f)
          then tau;; triggerUB
          else
            tau;;
            '(le2, vals) <- interp_imp ge (denote_exprs args) le1;;
            v <- trigger (Call f (vals↑));;
            tau;; tau;; v <- unwrapN (v↓);;
            tau;; tau;; Ret (alist_add x v le2, Vundef)
        | None => triggerUB
        end
      | _ => triggerUB
      end.
  Proof.
    rewrite denote_stmt_CallPtr. rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_GetName.
    des_ifs.
    1,5,6,7:(unfold triggerUB; grind).
    3:{ unfold unwrapU. grind. unfold triggerUB. grind. }
    - unfold unwrapU. grind. apply interp_imp_triggerUB.
    - unfold unwrapU. grind. apply interp_imp_Call_args.
  Qed.

  Lemma interp_imp_Syscall_args
        ge le0 x f args t
    :
      interp_imp ge (
                   eval_args <- (denote_exprs args);;
                   v <- trigger (Syscall f eval_args t);;
                   trigger (SetVar x v);; Ret Vundef) le0
      =
      '(le1, vals) <- interp_imp ge (denote_exprs args) le0;;
      v <- trigger (Syscall f vals t);;
      tau;; tau;; tau;; tau;;
      Ret (alist_add x v le1, Vundef).
  Proof.
    rewrite interp_imp_bind. grind.
    rewrite interp_imp_bind. rewrite interp_imp_Syscall. grind.
    rewrite interp_imp_bind. rewrite interp_imp_SetVar. grind.
    apply interp_imp_Ret.
  Qed.

  Lemma interp_imp_CallSys
        ge le0 x f args
    :
      interp_imp ge (denote_stmt (CallSys x f args)) le0 =
      '(le1, vals) <- interp_imp ge (denote_exprs args) le0;;
      v <- trigger (Syscall f vals top1);;
      tau;; tau;; tau;; tau;;
      Ret (alist_add x v le1, Vundef).
  Proof.
    rewrite denote_stmt_CallSys. apply interp_imp_Syscall_args.
  Qed.

  (* eval_imp  *)
  Lemma unfold_eval_imp
        ge fparams fvars fbody args
    :
      ` vret : val <- eval_imp ge (mk_function fparams fvars fbody) args ;; Ret (vret↑)
               =
               ` vret : val <-
                        (match init_args fparams args [] with
                         | Some iargs =>
                           ` x_ : lenv * val <-
                                  interp_imp ge (denote_stmt (fbody);; ` retv : val <- denote_expr (Var "return");; Ret retv) (init_lenv (fvars) ++ iargs);;
                                  (let (_, retv) := x_ in Ret retv)
                         | None => triggerUB
                         end) ;; Ret (vret↑).
  Proof.
    unfold eval_imp. ss.
  Qed.

  Lemma unfold_eval_imp_only
        ge f args
    :
      eval_imp ge f args
      =
      match init_args (fn_params f) args [] with
      | Some iargs =>
        ` x_ : lenv * val <-
               interp_imp ge (denote_stmt (fn_body f);; ` retv : val <- denote_expr (Var "return");; Ret retv) (init_lenv (fn_vars f) ++ iargs);;
               (let (_, retv) := x_ in Ret retv)
      | None => triggerUB
      end.
  Proof. ss. Qed.

End PROOFS.

(** tactics **)
Global Opaque denote_expr.
Global Opaque denote_stmt.
Global Opaque interp_imp.
Global Opaque eval_imp.

Require Import SimModSem.
Require Import HTactics.
Require Import ImpNotations.

Import ImpNotations.
(** tactic for imp-program reduction *)
Ltac imp_red :=
  cbn; try (rewrite interp_imp_bind);
  match goal with
  (** denote_stmt *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp_imp _ (denote_stmt (?stmt)) _))) ] =>
    match stmt with
    | Skip => rewrite interp_imp_Skip
    | Assign _ _ => rewrite interp_imp_Assign
    | Seq _ _ => rewrite interp_imp_Seq; imp_red
    | If _ _ _ => rewrite interp_imp_If
    | CallFun _ _ _ => rewrite interp_imp_CallFun
    | CallPtr _ _ _ => rewrite interp_imp_CallPtr
    | CallSys _ _ _ => rewrite interp_imp_CallSys
    | AddrOf _ _ => rewrite interp_imp_AddrOf
    | Malloc _ _ => rewrite interp_imp_Malloc
    | Free _ => rewrite interp_imp_Free
    | Load _ _ => rewrite interp_imp_Load
    | Store _ _ => rewrite interp_imp_Store
    | Cmp _ _ _ => rewrite interp_imp_Cmp
    | _ => fail
    end

      (** denote_expr *)
  | [ |- (gpaco6 (_sim_itree _) _ _ _ _ _ _ _ _ (_, ITree.bind' _ (interp_imp _ (denote_expr (?expr)) _))) ] =>
    match expr with
    | Var _ => rewrite interp_imp_expr_Var
    | Lit _ => rewrite interp_imp_expr_Lit
    | Plus _ _ => rewrite interp_imp_expr_Plus
    | Minus _ _ => rewrite interp_imp_expr_Minus
    | Mult _ _ => rewrite interp_imp_expr_Mult
    | Var_coerce _ => rewrite interp_imp_expr_Var
    | Lit_coerce _ => rewrite interp_imp_expr_Lit
    | _ => fail
    end

  | _ => idtac
  end.

Ltac imp_steps := repeat (repeat imp_red; steps).
