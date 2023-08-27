Require Import Coqlib.
Require Export ZArith.
Require Export String.
Require Export Any.
Require Export Axioms.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Skeleton.
Require Import ModSem Mod ModSemFacts ModFacts.
Require Import Algebra.
Require Import SimModSem.
Require Import ImpPrelude.
Require Import HTactics.

Set Implicit Arguments.

Local Open Scope nat_scope.

Module MEM.

  (* Refer to the memory module in CCR *)

  Definition callocF : list val -> itree Es val :=
    fun varg =>
      sz <- ((pargs [Tint] varg)?);;
      m0 <- trigger PGet;;
      ` m: Mem.t <- (m0↓)?;;
      d <- trigger (Choose _);;
      let m1 := Mem.mem_pad m d in
      let '(b, m2) := Mem.alloc m1 sz in
      trigger (PPut m2↑);;;
      Ret (Vptr (inl b) 0).

  Definition freeF : list val -> itree Es val :=
    fun varg =>
      '(b0, ofs) <- ((pargs [Tptr] varg)?);;
      ` b: nat <- (unl b0)?;;
      m0 <- trigger PGet;;
      ` m: Mem.t <- (m0↓)?;;
      m1 <- (Mem.free m b ofs)?;;
      trigger (PPut m1↑);;;
      Ret Vundef.

  Definition loadF : list val -> itree Es val :=
    fun varg =>
      '(b, ofs) <- ((pargs [Tptr] varg)?);;
      m0 <- trigger PGet;;
      ` m: Mem.t <- (m0↓)?;;
      v <- (Mem.load m b ofs)?;;
      Ret v.

  Definition storeF : list val -> itree Es val :=
    fun varg =>
      '(b, ofs, v) <- ((pargs [Tptr; Tuntyped] varg)?);;
      m0 <- trigger PGet;;
      ` m: Mem.t <- (m0↓)?;;
      m1 <- (Mem.store m b ofs v)?;;
      trigger (PPut m1↑);;;
      Ret Vundef.

  Definition cmpF : list val -> itree Es val :=
    fun varg =>
      '(v0, v1) <- ((pargs [Tuntyped; Tuntyped] varg)?);;
      m0 <- trigger PGet;;
      ` m: Mem.t <- (m0↓)?;;
      b <- (vcmp m v0 v1)?;;
      if (b: bool) then Ret (Vint 1%Z) else Ret (Vint 0%Z).

  Definition memMS_ (sk: Sk.t) : ModSem._t :=
    {|
      ModSem.fnsems :=
      [("calloc", cfunU callocF); ("free", cfunU freeF);
       ("load", cfunU loadF); ("store", cfunU storeF); ("cmp", cfunU cmpF)];
      ModSem.initial_st := (Mem.load_mem sk)↑;
    |}.

  Definition memMS (sk: Sk.t) : ModSem.t := Algebra.just (memMS_ sk).

  Definition memM: Mod.t :=
    {|
      Mod.get_modsem := memMS;
      Mod.sk := Sk.unit;
    |}.

End MEM.

Module VAR0.

  Definition initF : list val -> itree Es val :=
    fun varg =>
      _ <- ((pargs [] varg)?);;
      ` ptr: val <- ccallU "calloc" [Vint 1%Z];;
      _ <- trigger (PPut ptr↑);;
      Ret Vundef.

  Definition getF : list val -> itree Es val :=
    fun varg =>
      _ <- ((pargs [] varg)?);;
      ptr0 <- trigger (PGet);;
      ` ptr: val <- (ptr0↓)?;;
      ccallU "load" [ptr].

  Definition setF : list val -> itree Es val :=
    fun varg =>
      w <- ((pargs [Tint] varg)?);;
      ptr0 <- trigger (PGet);;
      ` ptr: val <- (ptr0↓)?;;
      ccallU "store" [ptr; (Vint w)].

  Definition varMS_ : ModSem._t :=
    {|
      ModSem.fnsems := [("init", cfunU initF); ("get", cfunU getF); ("set", cfunU setF)];
      ModSem.initial_st := Vnullptr↑;
    |}.

  Definition varMS : ModSem.t := Algebra.just varMS_.

End VAR0.
