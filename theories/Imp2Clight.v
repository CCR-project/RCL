Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.

From compcert Require Import AST Integers Ctypes Clight Globalenvs Linking Errors.

Import Int.

Set Implicit Arguments.

Section Compile_Mod.

  (* compile each module indiv, 
     prove behavior refinement for whole (closed) prog after linking *)
  Context `{Σ: GRA.t}.

  Context {s2p : string -> ident}.
  (* maybe use Int64.repr ? *)
  Context {to_long : Z -> int64}.

  (* initial gdefs = Imp.module, 
     contains single module's glob vars & internal funs. *)
  (* compile_stmt updates gdefs to include syscall defs. *)
  (* external funs (not syscall) : in other mod (resolved by linking) / 
     syscall : update gdefs dynamically by syntax *)
  (* no external variables: with weak typing, can resort to linking *)
  (* alloc/free should remain external (EF_malloc, EF_free)
     -> memory mod is not compiled with other Imps, 
     load/store are compiled in other way, so OK.
     cmp: ?? *)
  Let tgt_gdef := globdef (Ctypes.fundef function) type.
  Let tgt_gdefs := list (ident * tgt_gdef).

  Let Tlong0 :=
    (Tlong Signed noattr).

  Let Tptr0 tgt_ty :=
    (Tpointer tgt_ty noattr).

  Definition ident_key {T} id l : option T :=
    SetoidList.findA (Pos.eqb id) l.

  Definition string_key {T} l x : option T :=
    SetoidList.findA (String.string_dec x) l.

  Fixpoint compile_expr expr : option Clight.expr :=
    match expr with
    | Var x =>
      Some (Etempvar (s2p x) Tlong0)
    | Lit v =>
      match v with
      | Vint z => Some (Econst_long (to_long z) Tlong0)
      | _ => None
      end
    | Plus a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb =>
        Some (Ebinop Cop.Oadd ca cb Tlong0)
      | _, _ => None
      end
    | Minus a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb =>
        Some (Ebinop Cop.Osub ca cb Tlong0)
      | _, _ => None
      end
    | Mult a b =>
      match (compile_expr a), (compile_expr b) with
      | Some ca, Some cb =>
        Some (Ebinop Cop.Omul ca cb Tlong0)
      | _, _ => None
      end
    end
  .
  (** vsub, vmul may not agree with compcert's cop semantics *)

  (* for function pointer call *)
  Definition compile_expr_ptr tyargs expr : option Clight.expr :=
    match expr with
    | Var x =>
      Some (Etempvar (s2p x) (Tptr0 (Tfunction tyargs Tlong0 cc_default)))
    | _ => None
    end
  .

  Fixpoint compile_exprs (exprs: list Imp.expr) acc : option (list Clight.expr) :=
    match exprs with
    | h :: t =>
      do hexp <- (compile_expr h); compile_exprs t (acc ++ [hexp])
    | [] => Some acc
    end
  .

  (* only check number of arguments, exploit Tlong <-> Tptr64 *)
  Fixpoint cnt_args (tyargs: typelist) (args: list expr) : bool :=
    match tyargs, args with
    | Tnil, [] => true
    | Tcons ty tys, e::es => cnt_args tys es
    | _, _ => false
    end
  .

  Fixpoint args_to_typelist (args: list expr) : typelist :=
    match args with
    | [] => Tnil
    | h::t => Tcons Tlong0 (args_to_typelist t)
    end
  .

  Fixpoint typelist_to_typs (tl: typelist) : list typ :=
    match tl with
    | Tnil => []
    | Tcons h t => AST.Tlong :: (typelist_to_typs t)
    end
  .

  (* Imp has no type, value is either int64/ptr64 -> sem_cast can convert *)
  Fixpoint compile_stmt (g0: tgt_gdefs) stmt : option (tgt_gdefs * statement) :=
    match stmt with
    | Assign x e =>
      do ex <- (compile_expr e); Some (g0, Sset (s2p x) ex)
    | Seq s1 s2 =>
      do '(g1, cs1) <- (compile_stmt g0 s1);
      do '(g2, cs2) <- (compile_stmt g1 s2);
      Some (g2, Ssequence cs1 cs2)
    | If cond sif selse =>
      do cc <- (compile_expr cond);
      do '(g1, cif) <- (compile_stmt g0 sif);
      do '(g2, celse) <- (compile_stmt g1 selse);
      Some (g2, Sifthenelse cc cif celse)
    | Skip =>
      Some (g0, Sskip)

    | CallFun1 x f args =>
      do al <- (compile_exprs args []);
      Some
        (g0,
         Scall
           (Some (s2p x))
           (Evar (s2p f) (Tfunction (args_to_typelist al) Tlong0 cc_default))
           al)
    | CallFun2 f args =>
      do al <- (compile_exprs args []);
      Some
        (g0,
         Scall
           None
           (Evar (s2p f) (Tfunction (args_to_typelist al) Tlong0 cc_default))
           al)
      
    | CallPtr1 x pe args =>
      do al <- (compile_exprs args []);
      do a <- compile_expr_ptr (args_to_typelist al) pe;
      Some (g0, Scall (Some (s2p x)) a al)
    | CallPtr2 pe args =>
      do al <- (compile_exprs args []);
      do a <- compile_expr_ptr (args_to_typelist al) pe;
      Some (g0, Scall None a al)

    | CallSys1 x f args =>
      match ident_key (s2p f) g0 with
      | Some gd =>
        match gd with
        | Gfun fd =>
          match fd with
          | External ef tyargs tyres cconv =>
            do al <- (compile_exprs args []);
            if (cnt_args tyargs al)
            then
              Some
                (g0,
                 Scall
                   (Some (s2p x))
                   (Evar (s2p f) (Tfunction tyargs tyres cconv))
                   al)
            else None
          | _ => None
          end
        | _ => None
        end
      | None =>
        do al <- (compile_exprs args []);
        let tyargs := args_to_typelist al in
        let sg := mksignature (typelist_to_typs tyargs) (Tret AST.Tlong) cc_default in
        let fd := Gfun (External (EF_external f sg) tyargs Tlong0 cc_default) in
        let g1 := ((s2p f), fd)::g0 in
        Some
          (g1,
           Scall
             (Some (s2p x))
             (Evar (s2p f) (Tfunction tyargs Tlong0 cc_default))
             al)
      end
    | CallSys2 f args =>
      match ident_key (s2p f) g0 with
      | Some gd =>
        match gd with
        | Gfun fd =>
          match fd with
          | External ef tyargs tyres cconv =>
            do al <- (compile_exprs args []);
            if (cnt_args tyargs al)
            then
              Some
                (g0,
                 Scall
                   None
                   (Evar (s2p f) (Tfunction tyargs tyres cconv))
                   al)
            else None
          | _ => None
          end
        | _ => None
        end
      | None =>
        do al <- (compile_exprs args []);
        let tyargs := args_to_typelist al in
        let sg := mksignature (typelist_to_typs tyargs) (Tret AST.Tlong) cc_default in
        let fd := Gfun (External (EF_external f sg) tyargs Tlong0 cc_default) in
        let g1 := ((s2p f), fd)::g0 in
        Some
          (g1,
           Scall
             None
             (Evar (s2p f) (Tfunction tyargs Tlong0 cc_default))
             al)
      end

    | Expr r =>
      do cr <- (compile_expr r); Some (g0, Sreturn (Some cr))

    | AddrOf x GN =>
      (* GN: global name, g0 may not contain -> resolved by linking *)
      Some (g0, Sset (s2p x) (Eaddrof (Evar (s2p GN) Tlong0) Tlong0))
    | Load x pe =>
      do cpe <- (compile_expr pe); Some (g0, Sset (s2p x) (Ederef cpe Tlong0))
    | Store pe ve =>
      do cpe <- (compile_expr pe);
      do cve <- (compile_expr ve);
      Some (g0, Sassign (Ederef cpe Tlong0) cve)
    | Cmp x ae be =>
      do cae <- (compile_expr ae);
      do cbe <- (compile_expr be);
      let cmpexpr := (Ebinop Cop.Oeq cae cbe Tlong0) in
      Some (g0, Sset (s2p x) cmpexpr)
    end
  .

  (** memory accessing calls *)
  (** load, store, cmp are translated to non-function calls. *)
  (** need to register alloc and free in advance to be properly called *)
  Let alloc_def : Ctypes.fundef function :=
    External EF_malloc (Tcons Tlong0 Tnil) (Tptr0 Tlong0) cc_default.

  Let free_def : Ctypes.fundef function :=
    External EF_free (Tcons (Tptr0 Tlong0) Tnil) Tlong0 cc_default.

  Fixpoint compile_gVars (src : modVars) : tgt_gdefs :=
    match src with
    | [] => []
    | (name, v) :: t =>
      let init_value :=
          match v with
          | Vint z => [Init_int64 (to_long z)]
          | _ => [Init_int64 (to_long 0)]
          end in
      (s2p name, Gvar (mkglobvar Tlong0 init_value false false))::(compile_gVars t)
    end
  .

  (* g0 carries updated syscall defs found in compilation *)
  Fixpoint compile_gFuns (src : modFuns) g0 acc : option (tgt_gdefs * tgt_gdefs) :=
    match src with
    | [] => Some (g0, acc)
    | (name, f) :: t =>
      do '(g1, fbody) <- (compile_stmt g0 f.(Imp.fn_body));
      let fdef := {|
            fn_return := Tlong0;
            fn_callconv := cc_default;
            fn_params := (List.map (fun vn => (s2p vn, Tlong0)) f.(Imp.fn_params));
            fn_vars := [];
            fn_temps := (List.map (fun vn => (s2p vn, Tlong0)) f.(Imp.fn_vars));
            fn_body := fbody;
          |} in
      let gf := Internal fdef in
      compile_gFuns t g1 ((s2p name, Gfun gf)::acc)
    end
  .

  Definition compile_gdefs (src : Imp.module) : option tgt_gdefs :=
    let g0 := [(s2p "alloc", Gfun alloc_def); (s2p "free", Gfun free_def)] in
    do '(g_sys, g_fun) <- compile_gFuns src.(mod_funs) g0 [] ;
    let g_var := compile_gVars src.(mod_vars) in
    Some (g_sys ++ g_var ++ g_fun)
  .

  Variable src_name : mname.
  Variable src_defs : Imp.module.

  Definition compile :=
    let optdefs := (compile_gdefs src_defs) in
    match optdefs with
    | None => Error [MSG "statement compilation failed"]
    | Some defs =>
      make_program [] defs (List.map (fun '(i, g) => i) defs) (s2p "main")
    end
  .

End Compile_Mod.
