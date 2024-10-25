(** This file defines a minimalist locally nameless API for MetaCoq. *)

From MetaCoq.Utils Require Import utils MCList.
From MetaCoq.Template Require Import All.
From Repr Require Import Utils.

Import MCMonadNotation.

(** * Named Contexts. *)

Module NamedCtx.

(** A named context stores variable declarations indexed by identifiers [ident]. 
    We could use virtually anything in place of [ident],
    but this choice makes it easy to embed a variable in a term using [tVar]. 
    
    Introducing a declaration in the context shadows previous declarations with the same identifier.
*)
Record t := mk 
  { (** We store the [ident * context_decl] pairs in order, the most recent first. *)
    decls : list (ident * context_decl)
  ; (** The seed is used to generate fresh identifiers. *)
    seed : nat }.

(** The empty named context. *)
Definition empty : t := {| decls := [] ; seed := 0 |}.

(** Add a declaration to the context, shadowing previous declarations with the same identifier. *)
Definition push (ctx : t) (id : ident) (decl : context_decl) : t := 
  {| decls := (id, decl) :: ctx.(decls) ; seed := ctx.(seed) |}.

(** [fresh_ident basename ctx] builds a fresh identifier from [basename].
    It should be distinct from any other identifier constructed this way using [ctx]. *)
Definition fresh_ident (ctx : t) (basename : string) : ident * t :=
  let id := (basename ++ "#" ++ MCString.string_of_nat ctx.(seed))%bs in
  let ctx := {| decls := ctx.(decls) ; seed := ctx.(seed) + 1 |} in
  (id, ctx).

(** [get_decl id ctx] retrieves the most recent declaration for [id] in [ctx]. *)
Definition get_decl (ctx : t) (id : ident) : option context_decl :=
  List.find_map 
    (fun '(id', decl) => if id == id' then Some decl else None) 
    ctx.(decls).

(** Same as [get_decl] but returns only the name. *)
Definition get_name (ctx : t) (id : ident) : option aname :=
  option_map decl_name (get_decl ctx id).

(** Same as [get_decl] but returns only the type. *)
Definition get_type (ctx : t) (id : ident) : option term :=
  option_map decl_type (get_decl ctx id).

(** Same as [get_decl] but returns only the body. *)
Definition get_body (ctx : t) (id : ident) : option term :=
  decl_body =<< (get_decl ctx id).

End NamedCtx.

(** * Inspecting terms. *)

(** [with_decl ctx decl k] generates a fresh identifier built from [decl.(decl_name)], 
    adds the declaration [decl] to [ctx] and executes the continuation [k]
    in this augmented environment.
    It assumes [decl] contains no loose de Bruijn index. *)
Definition with_decl {T} (ctx : NamedCtx.t) (decl : context_decl) (k : NamedCtx.t -> ident -> T) : T :=
  (* Create a fresh identifier. *)
  let basename := 
    match decl.(decl_name).(binder_name) with 
    | nNamed n => n
    | nAnon => "x"%bs
    end
  in
  let (id, ctx) := NamedCtx.fresh_ident ctx basename in 
  (* Pass the identifier and extended context to the continuation. *)
  k (NamedCtx.push ctx id decl) id.

(** [with_context] generalizes [with_decl] to a de Bruijn context. 
    Beware of the order of variables : 
    - in a [context], the most recent (i.e. innermost) variables are at the head of the list.
    - in the continuation, the most recent variables are at the end of the list.  *)
Definition with_context {T} (ctx : NamedCtx.t) (decls : context) (k : NamedCtx.t -> list ident -> T) : T :=
  (* We process the declarations from outermost to innermost. *)
  let fix loop ctx ids decls :=
    match decls with 
    | [] => k ctx $ List.rev ids
    | d :: decls => 
      (* Don't forget to instantiate the loose de Bruijn indices in the local declaration [d]. *)
      with_decl ctx (map_decl (instantiate0 $ List.rev ids) d) $ fun ctx id =>
      loop ctx (id :: ids) decls
    end
  in 
  loop ctx [] $ List.rev decls.
  
(** [prod_telescope ctx (forall x1. ... forall xn. body) k] returns [k new_ctx [x1; ... ; xn]], 
    where [new_ctx] is [ctx] with bindings for the variables [x1] ... [xn]. 
    
    [prod_telescope] peels off binders until [body] is no longer a product. *)
Definition prod_telescope {T} (ctx : NamedCtx.t) (t : term) (k : NamedCtx.t -> list ident -> term -> T) : T :=
  let fix loop ctx ids t :=
    match t with 
    | tProd name ty body =>
      with_decl ctx {| decl_name := name ; decl_type := ty ; decl_body := None |} $ fun ctx id =>
      loop ctx (id :: ids) body
    | body => k ctx (List.rev ids) body
    end 
  in 
  loop ctx [] t.

(** [prod_telescope_n ctx max t k] is the same as [prod_telescope ctx t k], 
    but it stops after *at most* [max] products. *)
Definition prod_telescope_n {T} (ctx : NamedCtx.t) (n : nat) (t : term) (k : NamedCtx.t -> list ident -> term -> T) : T :=
  let fix loop ctx n ids t :=
    match n, t with 
    | S n, tProd name ty body =>
      with_decl ctx {| decl_name := name ; decl_type := ty ; decl_body := None |} $ fun ctx id =>
      loop ctx n (id :: ids) body
    | _, body => k ctx (List.rev ids) body
    end 
  in 
  loop ctx n [] t.

(** Same as [prod_telescope] but for lambda abstractions instead of products. *)
Definition lambda_telescope {T} (ctx : NamedCtx.t) (t : term) (k : NamedCtx.t -> list ident -> term -> T) : T :=
  let fix loop ctx ids t :=
    match t with 
    | tLambda name ty body =>
      with_decl ctx {| decl_name := name ; decl_type := ty ; decl_body := None |} $ fun ctx id => 
      loop ctx (id :: ids) body
    | body => k ctx (List.rev ids) body
    end 
  in 
  loop ctx [] t.
   
(** [lambda_telescope_n ctx max t k] is the same as [lambda_telescope ctx t k], 
    but it stops after *at most* [max] abstractions. *)
Definition lambda_telescope_n {T} (ctx : NamedCtx.t) (n : nat) (t : term) (k : NamedCtx.t -> list ident -> term -> T) : T :=
  let fix loop ctx n ids t :=
    match n, t with 
    | S n, tLambda name ty body =>
      with_decl ctx {| decl_name := name ; decl_type := ty ; decl_body := None |} $ fun ctx id =>
      loop ctx n (id :: ids) body
    | _, body => k ctx (List.rev ids) body
    end 
  in 
  loop ctx n [] t.

(** [with_ind_params ctx ind_body k] declares the parameters of the inductive [ind_body] in the local context,
    and executes [k] with the extended context and parameters. 
    - [k] takes the parameters ordered from first to last. *)
Definition with_ind_params {T} (ctx : NamedCtx.t) (ind_body : one_inductive_body) (k : NamedCtx.t -> list ident -> T) : T :=
  prod_telescope_n ctx (ind_param_count ind_body) ind_body.(ind_type) $ fun ctx params _ => k ctx params.

(** [with_ind_indices ctx ind_body params k] declares the indices of the inductive [ind_body] in the local context,
    and executes [k] with the extended context and indices. 
    - [k] takes the indices ordered from first to last.
    - [params] contains the parameters of the inductive, ordered from first to last. *)
Definition with_ind_indices {T} (ctx : NamedCtx.t) (ind_body : one_inductive_body) (params : list term) (k : NamedCtx.t -> list ident -> T) : T :=
  let indices := map_context_with_binders S (subst $ List.rev params) 0 ind_body.(ind_indices) in
  with_context ctx indices k.

(** [with_ctor_args ctx ctor_body params k] declares the arguments of the constructor [ctor_body] in the local context,
    and executes [k] with the extended context and arguments. 
    - [k] takes the arguments ordered from first to last.
    - [params] contains the parameters of the inductive, ordered from first to last. *)
Definition with_ctor_args {T} (ctx : NamedCtx.t) (ctor_body : constructor_body) (params : list term) (k : NamedCtx.t -> list ident -> T) : T :=
  let args := map_context_with_binders S (subst $ List.rev params) 0 ctor_body.(cstr_args) in
  with_context ctx args k.

(** * Constructing terms. *)

(** [mk_lambda ctx id body] creates the lambda abstraction [fun id => body].
    This assumes [id] is declared in [ctx].
   
    For instance here is how to create an identity function :
      [mk_lambda ctx x (tVar x)]
*)
Definition mk_lambda (ctx : NamedCtx.t) (id : ident) (body : term) : term :=
  match NamedCtx.get_decl ctx id with 
  | None => (* This should not happen. *) body
  | Some decl => tLambda decl.(decl_name) decl.(decl_type) $ abstract0 [id] body
  end.

(** [mk_prod ctx id body] creates the dependent product [forall id. body].
    This assumes [id] is declared in [ctx]. *)
Definition mk_prod (ctx : NamedCtx.t) (id : ident) (body : term) : term :=
  match NamedCtx.get_decl ctx id with 
  | None => (* This should not happen. *) body
  | Some decl => tProd decl.(decl_name) decl.(decl_type) $ abstract0 [id] body
  end.

(** [mk_case ctx ind ind_body scrutinee pred branches] builds a tCase term.
    - [params] contains the parameters of the inductive, from first to last.
    - [scrutinee] is the term we are matching on.
    - [pred] is a function of the form [fun ind_indices => fun scrutinee => return_type].
    - each branch is a function of the form [fun ctor_args => branch_body]. *)
Definition mk_case (ctx : NamedCtx.t) (ind : inductive) (ind_body : one_inductive_body) (params : list term) 
  (scrutinee : term) (pred : term) (branches : list term) : term :=
  (* [name_telescope n [] t k] peels off the lambdas in head position in [t],
     and passes the names of the bound variables and the body to [k].
     - the body is raw (it contains loose de Bruijn indices). 
     - the names are ordered from innermost to outermost.
     This performs no substitutions and is thus more efficient than [lambda_telescope_n]. *)
  let fix name_telescope {T} n names t (k : list aname -> term -> T) : T :=
    match n, t with 
    | S n, tLambda name _ t => name_telescope n (name :: names) t k
    | _, t => k names t
    end
  in 
  (* Case info. *)
  let case_info := {| ci_ind := ind ; ci_npar := ind_param_count ind_body ; ci_relevance := Relevant |} in
  (* Case predicate. *)
  let pred := 
    let n_indices := List.length ind_body.(ind_indices) in
    name_telescope (S n_indices) [] pred $ fun names ret =>
      {| puinst := [] ; pparams := params ; pcontext := names ; preturn := ret |}
  in
  (* Case branches. *)
  let on_branch ctor_body branch :=
    let n_args := List.length ctor_body.(cstr_args) in 
    name_telescope n_args [] branch $ fun names body =>
      {| bcontext := names ;  bbody := body |}
  in 
  tCase case_info pred scrutinee (map2 on_branch ind_body.(ind_ctors) branches).

(*Inductive myind (A B C : Set) : nat -> A -> B -> Set :=
| MyCtor : forall a b, C -> myind A B C 0 a b.

Definition test : TemplateMonad unit :=
mlet (env, t) <- tmQuoteRec myind ;;
mlet ind_body <- 
  match t with 
  | tInd ind _ =>
    match lookup_inductive env ind with 
    | Some (_, ind_body) => ret ind_body
    | _ => tmFail "Could not lookup inductive"
    end
  | _ => tmFail "Not an inductive"
  end
;;
mlet ctor_body <- 
  match ind_body.(ind_ctors) with 
  | [ ctor_body ] => ret ctor_body 
  | _ => tmFail "Invalid number of constructors"
  end
;;
let ctx := NamedCtx.empty in
with_ind_params ctx ind_body $ fun ctx params =>
with_ind_indices ctx ind_body (List.map tVar params) $ fun ctx indices =>
  tmPrint =<< tmEval cbv (List.map (fun a => NamedCtx.get_decl a ctx) indices).

MetaCoq Run test.*)
