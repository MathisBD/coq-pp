(** This file defines a minimalist locally nameless API for MetaCoq. *)

From MetaCoq.Utils Require Import utils MCList.
From MetaCoq.Template Require Import All.
From Repr Require Import Utils.
From ReductionEffect Require Import PrintingEffect.

Import MCMonadNotation.

(** I use an axiom for functions which are not total.
    Alternatives could be :
    1. use [option A] as the return type.
    2. use [M A] as the return type, where [M] is an error monad. 
    
    I went with an axiom because option 1 makes for really cumbersome syntax, 
    and option 2 requires a nice monad library. 
*)
Axiom failwith : forall A, string -> A.
Arguments failwith {_} _.

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

(** [size ctx] counts the number of declarations in [ctx]. *)
Definition size (ctx : t) : nat := List.length ctx.(decls).

(** Add a declaration to the context, shadowing previous declarations with the same identifier. *)
Definition push (ctx : t) (id : ident) (decl : context_decl) : t := 
  {| decls := (id, decl) :: ctx.(decls) ; seed := ctx.(seed) |}.

(** [fresh_ident basename ctx] builds a fresh identifier from [basename].
    It should be distinct from any other identifier constructed this way using [ctx]. *)
Definition fresh_ident (ctx : t) (basename : string) : ident * t :=
  let id := (basename ++ "__" ++ MCString.string_of_nat ctx.(seed))%bs in
  let ctx := {| decls := ctx.(decls) ; seed := ctx.(seed) + 1 |} in
  (id, ctx).

(** [get_decl id ctx] retrieves the [context_decl] for [id] in [ctx]. *)
Definition get_decl (ctx : t) (id : ident) : context_decl :=
  option_get (failwith "NamedCtx.get_decl") $
    List.find_map 
      (fun '(id', decl) => if id == id' then Some decl else None) 
      ctx.(decls).

(** [get_name id ctx] retrieves the [aname] of [id] in [ctx]. *)
Definition get_name (ctx : t) (id : ident) : aname := decl_name $ get_decl ctx id.

(** [get_type id ctx] retrieves the type of [id] in [ctx]. *)
Definition get_type (ctx : t) (id : ident) : term := decl_type $ get_decl ctx id.

(** [get_body id ctx] retrieves the body of [id] in [ctx]. *)
Definition get_body (ctx : t) (id : ident) : option term := decl_body $ get_decl ctx id.

End NamedCtx.

(** [mk_decl name ty] makes a declaration with given [name] and [ty],
    which additionally has no body and is [Relevant]. *)
Definition mk_decl (name : string) (ty : term) : context_decl :=
  {| decl_name := {| binder_name := nNamed name ; binder_relevance := Relevant |}
  ;  decl_type := ty
  ;  decl_body := None |}.

(** [fresh_evar ctx] generates a term representing a fresh evar in context [ctx]. *)
Definition fresh_evar (ctx : NamedCtx.t) : term :=
  let args := List.map (fun '(id, _) => tVar id) (NamedCtx.decls ctx) in
  tEvar fresh_evar_id args.

(** * Manipulagin inductives. *)

(** In MetaCoq the information related to an inductive type is spread accross
    three different datatypes : [inductive], [one_inductive_body] and [mutual_inductive_body].
    One often needs access to all three, so I package them in a single datatype. *)
Record packed_inductive := 
  { pi_ind : inductive
  ; pi_body : one_inductive_body 
  ; pi_mbody : mutual_inductive_body }.

(** Same as [packed_inductive] but for constructors. *)
Record packed_constructor :=
  { (** The inductive this constructor belongs to. *)
    pc_pi : packed_inductive 
  ; (** The index of this constructor. *)
    pc_idx : nat 
  ; (** The body of this constructor. *)
    pc_body : constructor_body }.

(** [pi_ctors pi] returns the list of [packed_constructors] of the 
    packed inductive [pi]. *)
Definition pi_ctors (pi : packed_inductive) : list packed_constructor :=
  mapi (fun i ctor => {| pc_pi := pi ; pc_idx := i ; pc_body := ctor |}) pi.(pi_body).(ind_ctors).

(** This works around a bug in metacoq. Eventually we should remove it. *)
Definition noccur_between := fix noccur_between (k n : nat) (t : term) {struct t} : bool :=
  match t with
  | tRel i => (i <? k) || (k + n <=? i)
  | tEvar _ args => forallb (noccur_between k n) args
  | tCast c _ t0 => noccur_between k n c && noccur_between k n t0
  | tProd _ T M | tLambda _ T M =>
	  noccur_between k n T && noccur_between (S k) n M
  | tLetIn _ b t0 b' =>
      noccur_between k n b && noccur_between k n t0 &&
      noccur_between (S k) n b'
  | tApp u v => noccur_between k n u && forallb (noccur_between k n) v
  | tCase _ p c brs =>
      let k' := #|pcontext p| + k in
      let p' :=
        test_predicate (fun _ : Instance.t => true) 
          (noccur_between k n) (noccur_between k' n) p in
      let brs' := test_branches_k (fun k0 : nat => noccur_between k0 n) k brs
        in
      p' && noccur_between k n c && brs'
  | tProj _ c => noccur_between k n c
  | tFix mfix _ | tCoFix mfix _ =>
      let k' := #|mfix| + k in
      forallb (test_def (noccur_between k n) (noccur_between k' n)) mfix
  | tArray _ arr def ty =>
      forallb (noccur_between k n) arr && noccur_between k n def &&
      noccur_between k n ty
  | _ => true
  end.

(** [is_pi_recursive pi] checks if the inductive [pi] is "recursive", in the sense
    that it appears as an argument to one of its constructors. *)
Definition is_pi_recursive (pi : packed_inductive) : bool := 
  let nparams := pi.(pi_mbody).(ind_npars) in
  (* The inductive is recursive if [tRel nparams] appears in the type of any argument. *)
  let is_ctor_rec pc := 
    List.existsb id $ mapi 
      (fun i arg => negb $ noccur_between (nparams + i) 1 arg.(decl_type)) 
      (List.rev pc.(pc_body).(cstr_args))
  in
  List.existsb is_ctor_rec $ pi_ctors pi.

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

(** [with_decls ctx [d_0; ... ; d_n] k] calls [with_decl] on [d_0] to [d_n] (in order).
    The declarations [d_i] must contain no loose de Bruijn index.
    A related but different variant is [with_context]. *)
Fixpoint with_decls {T} (ctx : NamedCtx.t) (ds : list context_decl) (k : NamedCtx.t -> list ident -> T) : T :=
  match ds with 
  | [] => k ctx [] 
  | d :: ds => 
    with_decl ctx d $ fun ctx id =>
    with_decls ctx ds $ fun ctx ids =>
      k ctx (id :: ids)
  end.

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
      with_decl ctx (map_decl (instantiate0 ids) d) $ fun ctx id =>
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

(** [with_ind_params ctx pi k] declares the parameters of the inductive [pi] in the local context,
    and executes [k] with the extended context and parameters. 
    - [k] takes the parameters ordered from first to last. *)
Definition with_ind_params {T} (ctx : NamedCtx.t) (pi : packed_inductive) 
  (k : NamedCtx.t -> list ident -> T) : T :=
  prod_telescope_n ctx pi.(pi_mbody).(ind_npars) pi.(pi_body).(ind_type) $ fun ctx params _ => 
    k ctx params.

(** [with_ind_indices ctx pi params k] declares the indices of the inductive [pi] in the local context,
    and executes [k] with the extended context and indices. 
    - [k] takes the indices ordered from first to last.
    - [params] contains the parameters of the inductive, ordered from first to last. *)
Definition with_ind_indices {T} (ctx : NamedCtx.t) (pi : packed_inductive) 
  (params : list term) (k : NamedCtx.t -> list ident -> T) : T :=
  let indices := map_context_with_binders S (subst $ List.rev params) 0 pi.(pi_body).(ind_indices) in
  with_context ctx indices k.

(** [with_ctor_args ctx pc params k] declares the arguments of the constructor [ctor_body] in the local context,
    and executes [k] with the extended context and arguments. 
    - [k] takes the arguments ordered from first to last.
    - [params] contains the parameters of the inductive, ordered from first to last. *)
Definition with_ctor_args {T} (ctx : NamedCtx.t) (pc : packed_constructor)
  (params : list term) (k : NamedCtx.t -> list ident -> T) : T :=
  (* Recall that the constructor arguments can depend on the inductive and on its parameters. *)
  let vars := List.rev (tInd pc.(pc_pi).(pi_ind) [] :: params) in
  let args := map_context_with_binders S (subst vars) 0 pc.(pc_body).(cstr_args) in
  with_context ctx args k.

(** [with_ctor_indices pc params k] gets the _values_ of the indices of the constructor [pc]
    (recall that the constructor indices can depend on the inductive [ind] and on the parameters [params]).
    - [k] takes the indices ordered from first to last.
    - [params] contains the parameters of the inductive, ordered from first to last. *)
Definition with_ctor_indices {T} (pc : packed_constructor) (params : list term) (k : list term -> T) : T :=
  (* Recall that the construtor indices can depend on the inductive and on its parameters. *)
  let vars := List.rev (tInd pc.(pc_pi).(pi_ind) [] :: params) in
  let indices := List.map (subst vars 0) pc.(pc_body).(cstr_indices) in
  k indices.

(** * Constructing terms. *)

(** [mk_lambdas ctx [id_0; ... ; id_n] body] creates the lambda abstraction 
    [fun id_0 ... id_n => body]. This assumes each [id_i] is declared in [ctx]. 
    
    For instance here is how to create an identity function :
      [mk_lambdas ctx [x] (tVar x)] *)
Definition mk_lambdas (ctx : NamedCtx.t) (ids : list ident) (body : term) : term :=
  let fix loop ids t :=
    match ids with 
    | [] => t
    | id :: ids => 
      let decl := NamedCtx.get_decl ctx id in
      loop ids $ tLambda decl.(decl_name) (abstract0 ids decl.(decl_type)) t
    end
  in 
  let ids := List.rev ids in 
  loop ids (abstract0 ids body).

(** [mk_prods ctx [id_0; ... ; id_n] body] creates the dependent product 
    [forall id_0 ... id_n. body]. This assumes each [id_i] is declared in [ctx]. *)
Definition mk_prods (ctx : NamedCtx.t) (ids : list ident) (body : term) : term :=
  let fix loop ids t :=
    match ids with 
    | [] => t
    | id :: ids => 
      let decl := NamedCtx.get_decl ctx id in
      loop ids $ tProd decl.(decl_name) (abstract0 ids decl.(decl_type)) t
    end
  in 
  let ids := List.rev ids in 
  loop ids (abstract0 ids body).
      
(** [mk_lets ctx [id_0; ... ; id_n] body] creates let-bindings 
    [let id_0 := def_0 in ... let id_n := def_n in body]. 
    
    This assumes each [id_i] is declared in [ctx] and has a [decl_body]. *)
Definition mk_lets (ctx : NamedCtx.t) (ids : list ident) (body : term) : term :=
  let fix loop ids t :=
    match ids with 
    | [] => t
    | id :: ids => 
      let decl := NamedCtx.get_decl ctx id in
      let d_ty := decl.(decl_type) in
      let d_body := option_get (failwith "mk_lets") $ decl.(decl_body) in
      loop ids $ tLetIn decl.(decl_name) (abstract0 ids d_body) (abstract0 ids d_ty) t
    end
  in 
  let ids := List.rev ids in 
  loop ids (abstract0 ids body).
    
(** [mk_pred ctx params indices x ret] creates a case predicate. 
    - [params] are the parameters of the inductive, ordered from first to last. 
    - [indices] are the indices of the inductive, ordered from first to last. 
    - [x] is the scrutinee of the match expression. 
    - [ret] is the return type of the match, which may depend on [indices] and [x]. *)
Definition mk_pred (ctx : NamedCtx.t) (params : list term) (indices : list ident) (x : ident) (ret : term) : predicate term :=
  let args := x :: List.rev indices in
  let names := List.map (NamedCtx.get_name ctx) args in 
  {| puinst := [] ; pparams := params ; pcontext := names ; preturn := abstract0 args ret |}.

(** [mk_branch ctx args body] creates a case branch.
    - [args] are the arguments of the branch, ordered from first to last.
    - [body] is the body of the branch, which may depend on [args]. *)
Definition mk_branch (ctx : NamedCtx.t) (args : list ident) (body : term) : branch term :=
  let args := List.rev args in
  let names := List.map (NamedCtx.get_name ctx) args in 
  {| bcontext := names ; bbody := abstract0 args body |}.

(** [mk_fix ctx id rarg body] creates a single fixpoint (not mutually recursive). 
    - [id] is the identifier of the fixpoint parameter. 
    - [rarg] is the index of the recursive argument of the fixpoint (starting at 0). 
    - [body] is the body of the fixpoint, which can contain [id]. *)
Definition mk_fix (ctx : NamedCtx.t) (id : ident) (rec_arg_idx : nat) (body : term) : term :=
  let def := 
    {| dname := NamedCtx.get_name ctx id 
    ;  dtype := NamedCtx.get_type ctx id 
    ;  dbody := abstract0 [id] body 
    ;  rarg := rec_arg_idx |}
  in 
  tFix [def] 0.
