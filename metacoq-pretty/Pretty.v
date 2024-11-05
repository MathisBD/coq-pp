From Coq Require Import Uint63 PrimString List Bool.
From MetaCoq.Template Require Import All.
From PPrint Require Import All.

Import ListNotations MCMonadNotation.
Open Scope pstring.

(** * Utils *)

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) (at level 10, x at level 100, right associativity, only parsing).

(** Some notations to avoid confusing string types. *)
Notation pstring := PrimString.string.
Notation bstring := bytestring.string.

(** Convert a bytestring to a primitive string. *)
Definition pstring_of_sbtring (bstr : bstring) : pstring :=
  let fix loop pstr bstr :=
    match bstr with 
    | String.EmptyString => pstr
    | String.String byte bstr => 
      let char := PrimString.make 1 $ Uint63.of_nat (Byte.to_nat byte) in
      loop (PrimString.cat pstr char) bstr
    end
  in
  loop "" bstr.

(** Convert a primitive string to a byte string. *)
Definition bstring_of_pstring (pstr : pstring) : bstring :=
  string_of_list char63_to_string (PrimStringAxioms.to_list pstr).

(** [bstr s] builds an atomic document containing the bytestring [s]. *)
Definition bstr {A} (s : bstring) : doc A :=
  str $ pstring_of_sbtring s.

(** Name handling. *)

(** While pretty-printing terms we store the names of the binders traversed so far
    in a _name context_ [id_0; id_1; ...; id_n], which is simply a list of [ident]. 
    The identifier [id_i] is the name associated to the de Bruijn index [i]. *)

Section NameHandling.
Context (env : global_env_ext).

(** [is_fresh ctx id] checks if [id] does not occur in context [ctx]. *)
Definition is_fresh (ctx : list ident) (id : ident) :=
  List.forallb (fun id' => negb (eqb id id')) ctx.

(** [name_for_type t] chooses a generic name for a variable of type [t]. *)
Fixpoint name_for_type (t : term) : bstring :=
  match t with
  | tRel _ | tVar _ | tEvar _ _ => "H"%bs
  | tSort _ => "X"%bs
  | tProd _ _ _ => "f"%bs
  | tLambda _ _ _ => "f"%bs
  | tLetIn _ _ _ t' => name_for_type t'
  | tApp f _ => name_for_type f
  | tConst _ _ => "x"%bs
  | tInd ind u =>
    match lookup_inductive env ind with
    | Some (_, body) => String.substring 0 1 (body.(ind_name))
    | None => "X"%bs
    end
  | _ => "U"%bs
  end.

(** [base_name n ty] creates a generic name from :
    - [n] if it is not anonymous.
    - [ty] otherwise. *)
Definition base_name (n : name) (t : option term) : ident :=
  match n with
  | nNamed n => n
  | nAnon =>
    match t with
    | Some t => name_for_type t
    | None => "_"%bs
    end
  end.

(** [fresh_name ctx basename] generates a fresh name in context [ctx],
    starting from [basename]. *)
Definition fresh_name (ctx : list ident) (basename : ident) : ident :=
  (* Try without any suffix. *)
  if is_fresh ctx basename then basename
  (* Try suffixes, starting at 0 and couting up. *)
  else 
    let fix loop i fuel :=
      let name := (basename ++ string_of_nat i)%bs in
      match fuel with 
      | 0 => (* This should not happen. *) name
      | S fuel => if is_fresh ctx name then name else loop (S i) fuel
      end
    in 
    (* This fuel value should be big enough. *)
    loop 0 (List.length ctx).

(** Get the [context] associated to a fixpoint. *)
Definition fix_context (m : mfixpoint term) : context :=
  List.rev (mapi (fun i def => vass def.(dname) (lift0 i def.(dtype))) m).

(** [push_context decls ctx] adds fresh names for the declarations [decls]
    to the name context [ctx]. *)
Definition push_context (decls : context) (ctx : list ident) : list ident :=
  let fix loop decls ctx :=
    match decls with
    | [] => ctx
    | d :: decls => 
      let basename := base_name (binder_name d.(decl_name)) (Some d.(decl_type)) in
      loop decls (fresh_name ctx basename :: ctx)
    end 
  in
  loop (MCList.rev decls) ctx.

Definition string_of_constructor (ind : inductive) (ctor_idx : nat) : bstring :=
  (string_of_inductive ind ++ "," ++ string_of_nat ctor_idx)%bs.

End NameHandling.

(** * Pretty-printing configuration. *)

Module Config.

(** The pretty-printing functions can show a variable amount of information,
    depending on the printing configuration. *)
Record t := mk
  { (** Should we print universes ? *)
    with_universes : bool 
  ; (** Should we print evar instances ? *)
    with_evar_instances : bool 
  ; (** Should we print relevance information ? *)
    with_relevance : bool 
  ; (** Should we print match predicates ? *)
    with_match_preds : bool
  ; (** Should we print all parentheses ? *) 
    with_parentheses : bool }.

(** Don't print any low-level details. *)
Definition basic : t := mk false false false false false.
  
(** Print all low-level details. *)
Definition all : t := mk true true true true true.
  
End Config.

(** Pretty-printing. *)

Section Printing.
Context (config : Config.t).
Context (env : global_env_ext).

(** [paren_if top d] adds parentheses around document [d] if [top] is equal to [false].
    It takes into account the configuration option to force parentheses. *)
Definition paren_if {A} (top : bool) (d : doc A) : doc A :=
  if Config.with_parentheses config || negb top then paren d else d.
  
Definition print_name (n : name) : doc unit :=
  match n with 
  | nAnon => str "_"
  | nNamed n => bstr n
  end. 

Definition print_kername (kn : kername) : doc unit :=
  bstr $ snd kn.

Definition print_level (l : Level.t) : doc unit :=
  match l with 
  | Level.lzero => str "Set"
  | Level.level s => bstr s
  | Level.lvar n => str "lvar" ^^ nat10 n
  end.

Definition print_level_expr (le : LevelExprSet.elt) : doc unit :=
  match le with 
  | (l, 0) => print_level l
  | (l, n) => print_level l ^^ str "+" ^^ nat10 n
  end.
  
Definition print_sort (s : sort) :=
  match s with
  | sProp => str "Prop"
  | sSProp => str "SProp"
  | sType l =>
    if Config.with_universes config
    then
      let lvls := flow_map (str ";" ^^ break 0) print_level_expr $ LevelExprSet.elements l in 
      bracket "Type(" lvls ")"
    else str "Type"
  end.

Definition print_univ_instance (uinst : Instance.t) : doc unit :=
  if Config.with_universes config && negb (uinst == []) then 
    let lvls := flow_map (break 0) print_level uinst in 
    bracket "@{" lvls "}"
  else 
    empty.

(** Helper function to print a single definition in a fixpoint block. *)
Definition print_def {A} (on_ty : A -> doc unit) (on_body : A -> doc unit) (def : def A) :=
  let n_doc := 
    separate space 
      [ print_name (binder_name $ def.(dname)) 
      ; str "{ struct" ^+^ nat10 def.(rarg) ^+^ str "}" 
      ; str ":" ] 
  in
  let ty_doc := on_ty def.(dtype) ^+^ str ":=" in
  let body_doc := on_body def.(dbody) in 
  (* We don't [align] here on purpose. *)
  group $ group (n_doc ^//^ ty_doc) ^//^ body_doc.
               
(** Helper function to print a single term of the form [tFix mfix n] or [tCoFix mfix n].
    The parameter [is_fix] controls whether to print a fixpoint or a co-fixpoint. *)
Definition print_fixpoint (on_term : list ident -> term -> doc unit) (ctx : list ident) 
  (defs : mfixpoint term) (n : nat) (is_fix : bool) : doc unit  :=
  let prefix := if is_fix then str "let fix" else str "let cofix" in
  let sep := break 0 ^^ str "with" ^^ space in
  let on_def := 
    print_def (on_term ctx) (on_term $ push_context env (fix_context defs) ctx)
  in
  let func_name := 
    option_default 
      (fun def => print_name def.(dname).(binder_name)) 
      (List.nth_error defs n) (nat10 n) 
  in
  if Nat.ltb 1 (List.length defs)
  then align $ group $ prefix ^+^ separate_map sep on_def defs ^/^ str "for" ^+^ func_name
  else align $ group $ prefix ^+^ separate_map sep on_def defs.

(** Helper function to print a single branch (without the leading "|"). *)
Definition print_branch (on_term : list ident -> term -> doc unit) (ctx : list ident) 
  (branch : branch term) (ctor : constructor_body) : doc unit :=
  let branch_ctx := push_context env ctor.(cstr_args) ctx in
  let var_names := List.rev (firstn (List.length ctor.(cstr_args)) branch_ctx) in
  let binder := flow_map (break 2) bstr (ctor.(cstr_name) :: var_names) in
  group $ align $ binder ^+^ str "⇒" ^//^ on_term branch_ctx branch.(bbody).

Fixpoint print_term (top : bool) (ctx : list ident) (t : term) {struct t} : doc unit :=
  match t with
  | tRel n =>
    match List.nth_error ctx n with
    | Some id => bstr id
    | None => str "UnboundRel(" ^^ nat10 n ^^ str ")"
    end
  | tVar n => str "Var(" ^^ bstr n ^^ str ")"
  | tEvar ev args => 
    if Config.with_evar_instances config then 
      let args_doc := flow_map (str ";" ^^ break 0) (print_term true ctx) args in
      str "Evar(" ^^ nat10 ev ^^ bracket "[" args_doc "]" ^^ str ")"
    else 
      str "Evar(" ^^ nat10 ev ^^ str ")"
  | tSort s => print_sort s
  | tCast c _ t => 
    let contents := print_term true ctx c ^//^ (str ":"  ^+^ print_term true ctx t) in
    paren_if top $ align $ group contents
  | tProd n ty body =>
    let n := fresh_name ctx $ base_name env n.(binder_name) (Some ty) in
    let contents :=
      (* Decide whether this is a dependent or non-dependent product. *)
      if noccur_between 0 1 body
      then [print_term false ctx ty ^+^ str "→" ; print_term true (n :: ctx) body]
      else [str "∀" ^+^ bstr n ^+^ str ":" ; 
            print_term false ctx ty ^^ str "," ; 
            print_term true (n :: ctx) body]
    in 
    paren_if top $ align $ flow (break 2) contents
  | tLambda n ty body =>
    let n := fresh_name ctx $ base_name env n.(binder_name) (Some ty) in
    let contents :=
      [str "fun" ^+^ bstr n ^+^ str ":" ; 
       print_term true ctx ty ^+^ str "⇒" ; 
       print_term true (n :: ctx) body]
    in 
    paren_if top $ align $ flow (break 2) contents
  | tLetIn n def ty body =>
    let n := fresh_name ctx $ base_name env n.(binder_name) (Some ty) in
    let n_doc := str "let" ^+^ bstr n ^+^ str ":" in
    let ty_doc := print_term true ctx ty ^+^ str ":=" in
    let def_doc := print_term true ctx def in
    let body_doc := group (str "in" ^/^ print_term true (n :: ctx) body) in
    (* Getting the formatting correct is a bit tricky. *)
    group $ align $ 
      group (n_doc ^//^ ty_doc) ^//^ def_doc ^/^ body_doc
  | tApp f args =>
    paren_if top $ align $ flow_map (break 2) (print_term false ctx) (f :: args) 
  | tConst kname uinst => print_kername kname ^^ print_univ_instance uinst
  | tInd ind uinst =>
    let name := 
      match lookup_inductive env ind with
      | Some (_, body) => bstr body.(ind_name)
      | None => bracket "UnboundInd(" (bstr $ string_of_inductive ind) ")"
      end
    in 
    name ^^ print_univ_instance uinst
  | tConstruct ind idx uinst =>
    let name :=
      match lookup_constructor env ind idx with
      | Some (_, body) => bstr body.(cstr_name)
      | None =>
        str "UnboundCtor(" ^^ (bstr $ string_of_constructor ind idx) ^^ str ")"
      end
    in
    name ^^ print_univ_instance uinst
  | tCase ci pred x branches =>
    match lookup_inductive env ci.(ci_ind) with
    | Some (_, body) =>
        (* Print each branch separately. *)
        let branch_docs := map2 (print_branch (print_term true) ctx) branches body.(ind_ctors) in
        (* Part 1 is [match x with]. *)
        let part1 := 
          group $ str "match" ^+^ align (print_term true ctx x) ^/^ str "with"
        in
        (* Part 2 is [C1 => ... | C2 => ... | C3 => ... end]*)
        let part2 := 
          group $ concat 
            [ break 0 ^^ ifflat empty (str "|" ^^ space)
            ; separate (break 0 ^^ str "|" ^^ space) branch_docs
            ; break 0 ^^ str "end" ]
        in
        paren_if top $ align $ part1 ^^ part2
    | None => str "CASE_ERROR"
    end
  | tFix mfix n => paren_if top $ print_fixpoint (print_term true) ctx mfix n true 
  | tCoFix mfix n => paren_if top $ print_fixpoint (print_term true) ctx mfix n false
  | tProj p t =>
    match lookup_projection env p with
    | Some (_, _, _, pbody) => 
      group $ align $ concat 
        [ print_term false ctx t
        ; ifflat empty (hardline ^^ blank 2) 
        ; str ".(" ^^ bstr pbody.(proj_name) ^^ str ")" ]
    | None =>
      let contents := 
        [ bstr (string_of_inductive p.(proj_ind)) 
        ; nat10 p.(proj_npars)
        ; nat10 p.(proj_arg) 
        ; print_term true ctx t ]
      in
      bracket "UnboundProj(" (flow (str "," ^^ break 0) contents) ")"
    end 
  | tInt i => str "Int(" ^^ bstr (string_of_prim_int i) ^^ str ")"
  | tFloat f => str "Float(" ^^ bstr (string_of_float f) ^^ str ")"
  | tString s => str "String(" ^^ str s ^^ str ")"
  | tArray u arr def ty => 
    let arr_doc := bracket "[" (flow_map (space ^^ str ";" ^^ break 0) (print_term true ctx) arr) "]" in 
    let contents := [print_level u ; arr_doc ; print_term true ctx def ; print_term true ctx ty] in
    bracket "Array(" (flow (str "," ^^ break 0) contents) ")"
  end.

(*Definition test : TemplateMonad unit :=
  mlet (env, t) <- tmQuoteRec 
    (fix add (n m : nat) {struct n} : nat :=
    match n with
    | 0 => m
    | S p => S (add p m)
    end) ;;
  let output := pp_string 80 $ print_term Config.basic (empty_ext env) true [] t in
  tmPrint =<< tmEval cbv output.
MetaCoq Run test. *)

Definition print_context_decl (ctx : list ident) (decl : context_decl) : ident * doc unit :=
  match decl.(body) with
  | None =>
  | Some body => 
  | {| decl_name := n; decl_type := ty; decl_body := None |} =>
    let na' := (fresh_name Σ Γ na.(binder_name) (Some ty)) in
    (na', ("(" ^ na' ^ " : " ^ print_term Γ true ty ^ ")"))
  | {| decl_name := na; decl_type := ty; decl_body := Some b |} =>
    let na' := (fresh_name Σ Γ na.(binder_name) (Some ty)) in
    (na', ("(" ^ na' ^ " : " ^ print_term Γ true ty ^ " := " ^
      print_term Γ true b ^ ")"))
  end.

Fixpoint print_context Γ Δ : list ident * t :=
  match Δ with
  | [] => (Γ, "" : t)
  | d :: decls =>
    let '(Γ, s) := print_context Γ decls in
    let '(na, s') := pr_context_decl Γ d in
    match decls with
    | [] => (na :: Γ, s ^ s')
    | _ => (na :: Γ, s ^ " " ^ s')
    end
  end.

Definition print_one_cstr Γ (mib : mutual_inductive_body) (c : constructor_body) : t :=
  let '(Γargs, s) := print_context Γ c.(cstr_args) in
  c.(cstr_name) ^ " : " ^ s ^ "_" ^ print_list (print_term Γargs true) " " c.(cstr_indices).

Definition print_one_ind (short : bool) Γ (mib : mutual_inductive_body) (oib : one_inductive_body) : t :=
  let '(Γpars, spars) := print_context Γ mib.(ind_params) in
  let '(Γinds, sinds) := print_context Γpars oib.(ind_indices) in
  oib.(ind_name) ^ spars ^ sinds ^ print_term Γinds true (tSort oib.(ind_sort)) ^ ":=" ^ nl ^
  if short then "..."
  else print_list (print_one_cstr Γpars mib) nl oib.(ind_ctors).

Definition print_one_cstr_entry Γ (mie : mutual_inductive_entry) (c : ident × term) : t :=
  c.1 ^ " : " ^ print_term Γ true c.2.

Definition print_one_ind_entry (short : bool) Γ (mie : mutual_inductive_entry) (oie : one_inductive_entry) : t :=
  let '(Γpars, spars) := print_context Γ mie.(mind_entry_params) in
  oie.(mind_entry_typename) ^ spars ^ print_term Γpars true oie.(mind_entry_arity) ^ ":=" ^ nl ^
  if short then "..."
  else print_list (print_one_cstr_entry Γpars mie) nl (combine oie.(mind_entry_consnames) oie.(mind_entry_lc)).

End env.

Definition universes_decl_of_universes_entry e :=
  match e with
  | Monomorphic_entry ctx => Monomorphic_ctx
  | Polymorphic_entry uctx => Polymorphic_ctx (fst uctx, snd (snd uctx))
  end.
Definition print_recursivity_kind k :=
  match k with
  | Finite => "Inductive"
  | CoFinite => "CoInductive"
  | BiFinite => "Variant"
  end.
Definition print_mib Σ with_universes (short : bool) (mib : mutual_inductive_body) : t :=
  let Σ' := (Σ, mib.(ind_universes)) in
  let names := fresh_names Σ' [] (arities_context mib.(ind_bodies)) in
    (print_recursivity_kind mib.(ind_finite) ^ " " ^
    print_list (print_one_ind Σ' with_universes short names mib) (nl ^ "with ") mib.(ind_bodies) ^ "." ^ nl).
Definition mie_arities_context mie :=
  rev_map (fun ind => vass (mkBindAnn (nNamed ind.(mind_entry_typename)) Relevant)
    (it_mkProd_or_LetIn mie.(mind_entry_params) ind.(mind_entry_arity)))
    mie.(mind_entry_inds).
Definition print_mie Σ with_universes (short : bool) (mie : mutual_inductive_entry) : t :=
  let Σ' := (Σ, universes_decl_of_universes_entry mie.(mind_entry_universes)) in
  let names := fresh_names Σ' [] (mie_arities_context mie) in
    (print_recursivity_kind mie.(mind_entry_finite) ^ " " ^
    print_list (print_one_ind_entry Σ' with_universes short names mie) (nl ^ "with ") mie.(mind_entry_inds) ^ "." ^ nl).
Fixpoint print_env_aux with_universes (short : bool) (prefix : nat) (Σ : global_env) (acc : t) : t :=
  match prefix with
  | 0 => match Σ.(declarations) with [] => acc | _ => ("..." ^ nl ^ acc) end
  | S n =>
    let univs := Σ.(Env.universes) in
    let retro := Σ.(Env.retroknowledge) in
    match Σ.(declarations) with
    | [] => acc
    | (kn, InductiveDecl mib) :: Σ =>
      let Σ := {| Env.universes := univs; declarations := Σ; retroknowledge := retro |} in
      print_env_aux with_universes short n Σ (print_mib Σ with_universes short mib ^ acc)
    | (kn, ConstantDecl cb) :: Σ =>
      let Σ' := ({| Env.universes := univs; declarations := Σ; retroknowledge := retro |}, cb.(cst_universes)) in
      print_env_aux with_universes short n Σ'.1
        ((match cb.(cst_body) with
          | Some _ => "Definition "
          | None => "Axiom "
        end) ^ string_of_kername kn ^ " : " ^ print_term Σ' with_universes nil true cb.(cst_type) ^
        match cb.(cst_body) with
        | Some b =>
          if short then ("..." ^ nl)
          else (" := " ^ nl ^ print_term Σ' with_universes nil true b ^ "." ^ nl)
        | None => "."
        end ^ acc)
    end
  end.
Definition print_env with_universes (short : bool) (prefix : nat) Σ :=
  print_env_aux with_universes short prefix Σ (Tree.string "").
Definition print_program with_universes (short : bool) (prefix : nat) (p : program) : t :=
  print_env with_universes short prefix (fst p) ^ nl ^ print_term (empty_ext (fst p)) with_universes nil true (snd p).
d PrintTermTree.
finition print_mie Σ with_universes short := Tree.to_string ∘ PrintTermTree.print_mie Σ with_universes short.
finition print_mib Σ with_universes short := Tree.to_string ∘ PrintTermTree.print_mib Σ with_universes short.
efinition print_term Σ Γ top := Tree.to_string ∘ PrintTermTree.print_term Σ true Γ top.

Definition print_env (short : bool) (prefix : nat) Σ :=
  Tree.to_string (PrintTermTree.print_env true short prefix Σ).

Definition print_program (short : bool) (prefix : nat) (p : program) : string :=
  Tree.to_string (PrintTermTree.print_program true short prefix p).
