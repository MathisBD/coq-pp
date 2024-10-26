(** This file implements a Coq command that automatically derives [Repr] instances
    for inductives and records. *)

From MetaCoq.Template Require Import All.
From MetaCoq.Utils Require Import monad_utils.
From Coq Require Import List String.
From PPrint Require Import All.
From Repr Require Import Class Utils LocallyNameless Class.

Import ListNotations MCMonadNotation.


(** Pretty-print the application of constructor [label] to a list of arguments [args]. *)
Definition repr_ctor (label : string) (args : list (doc unit)) : doc unit :=
  (*let res := separate (break 1) (str label :: args) in*)
  let res := flow (break 1) (str label :: args) in
  group (hang 4 res).

Inductive tree A :=
  | Leaf : tree A
  | Node : A -> tree A -> tree A -> tree A.

Definition repr_tree (A : Type) (RA : Repr A) : Repr (tree A) :=
  Build_Repr (tree A) $ 
    fix f (xs : tree A) : doc unit :=
      let _ := Build_Repr (tree A) f in 
      match xs with 
      | Leaf => repr_ctor "Leaf" []
      | Node x l r => repr_ctor "Node" [repr_doc x; repr_doc l; repr_doc r]
      end.

Instance : Repr bool := { repr_doc b := if b then str "true" else str "false" }.
Existing Instance repr_tree.

Arguments Leaf {A}.
Arguments Node {A}.

Eval compute in repr $ Node true Leaf (Node false Leaf Leaf).



(** Quote some terms that we will need below. *)
MetaCoq Quote Definition quoted_repr_doc := (@repr_doc).
MetaCoq Quote Definition quoted_repr_ctor := (repr_ctor).
MetaCoq Quote Definition quoted_doc_unit := (doc unit).
MetaCoq Quote Definition quoted_nil := (@nil).
MetaCoq Quote Definition quoted_cons := (@cons).
MetaCoq Quote Definition quoted_Repr := (Repr).
MetaCoq Quote Definition quoted_Build_Repr := (Build_Repr).

(** [term_list ty xs] builds the term corresponding to the list [x1; ...; xn], 
    assuming each [xi] has type [ty]. *)
Fixpoint term_list (ty : term) (xs : list term) : term :=
  match xs with 
  | [] => mkApp quoted_nil ty
  | x :: xs => mkApps quoted_cons [ty; x; term_list ty xs]
  end.

(** Build a single argument. *)
Definition build_arg ctx (arg : ident) : term :=
  (* I use an evar in place of the [Repr] instance, which will be solved when unquoting the term. *)
  ret $ mkApps quoted_repr_doc [NamedCtx.get_type ctx arg; fresh_evar ctx; tVar arg].

(** Build a branch for a single constructor. *)
Definition build_branch ctx (params : list term) (ctor_body : constructor_body) (quoted_ctor_name : term) : branch term :=
  (* Get the list of arguments of the constructor. *)
  with_ctor_args ctx ctor_body params $ fun ctx args =>
  (* Apply [repr_ctor] to the label and the arguments. *)
  let repr_args := term_list quoted_doc_unit $ List.map (build_arg ctx) args in
  mk_branch ctx args $ mkApps quoted_repr_ctor [quoted_ctor_name; repr_args].

(** Derive the [repr_doc] function for an inductive type. *)
Definition build_func ctx (ind : inductive) (ind_body : one_inductive_body) 
  (params : list term) (ctor_names : list term) : term :=
  (* Declare the input parameter [x]. *)
  with_decl ctx (mk_decl "x"%bs $ mkApps (tInd ind []) params) $ fun ctx x =>  
  (* Case info. *)  
  let ci := {| ci_ind := ind ; ci_npar := List.length params ; ci_relevance := Relevant |} in
  (* Case predicate. *)
  let pred := 
    with_ind_indices ctx ind_body params $ fun ctx indices =>
    with_decl ctx (mk_decl "x"%bs $ mkApps (tInd ind []) params) $ fun ctx x => 
      mk_pred ctx params indices x quoted_doc_unit
  in
  (* Case branches. *)
  let branches := map2 (build_branch ctx params) ind_body.(ind_ctors) ctor_names in
  (* Bind the input parameter. *)
  mk_lambdas ctx [x] $ tCase ci pred (tVar x) branches.

Definition build_inst ctx (ind : inductive) (ind_body : one_inductive_body) (ctor_names : list term) : term :=
  (* Declare the parameters of the inductive. *)
  with_ind_params ctx ind_body $ fun ctx params =>  
  (* Declare a [Repr] instance for each parameter. *)
  let repr_decls := 
    List.map (fun p => mk_decl "H"%bs $ mkApp quoted_Repr $ tVar p) params 
  in
  with_decls ctx repr_decls $ fun ctx param_insts =>
  (* Build the [repr_doc] function. *)
  let f := build_func ctx ind ind_body (List.map tVar params) ctor_names in
  (* Package it in a [Repr] record. *)
  let record := mkApps quoted_Build_Repr [mkApps (tInd ind []) $ List.map tVar params; f] in
  (* Abstract over the parameters and repr instances. *)
  mk_lambdas ctx (List.app params $ param_insts) record.

(** [env_of_term ts] returns the global environment needed to type the terms in [ts]. 

    This function is maybe slower than it should be (I use [merge_global_envs] a lot).
    If performance becomes an issue you can try calling [tmQuoteRec] only once,
    on the list of unquoted terms. I tried this approach but failed to deal
    with the dependent typing and universe issues it caused (all the terms in [ts] might
    have different types).
*)
Fixpoint env_of_terms (ts : list term) : TemplateMonad global_env :=
  match ts with 
  | [] => tmReturn empty_global_env
  | t :: ts =>
    (* Get the environment for [t]. *)
    mlet t <- tmUnquote t ;;
    mlet (t_env, _) <- tmQuoteRec (my_projT2 t) ;;
    (* Get the environment for [ts]. *)
    mlet ts_env <- env_of_terms ts ;;
    (* Merge both envs. *)
    tmReturn (merge_global_envs t_env ts_env)
  end.

(** Derive command entry-point. *)
Definition derive (ind : inductive) : TemplateMonad unit :=
  (* Get the global environment needed to type the inductive. *)
  mlet t_doc <- tmQuote doc ;;
  mlet t_unit <- tmQuote unit ;;
  mlet env <- env_of_terms [tInd ind []; t_unit ; t_doc] ;;
  (* Get the inductive body. *)
  mlet ind_body <- 
    match lookup_inductive env ind with 
    | None => tmFail "Failed looking up the inductive body"%bs
    | Some (_, ind_body) => ret ind_body 
    end 
  ;;
  (* Quote the constructor names. *)
  mlet ctor_names <- 
    monad_map 
      (fun c => tmQuote =<< tmEval cbv (bytestring.String.to_string c.(cstr_name))) 
      ind_body.(ind_ctors)
  ;;
  (* Derive the [Repr] instance. *)
  let instance := build_inst NamedCtx.empty ind ind_body ctor_names in
  tmPrint =<< tmEval cbv instance ;;
  (*tmPrint =<< tmEval cbv (print_term (env, Monomorphic_ctx) [] true instance) ;;*)
  (* Add the instance to the global environment and register it as an instance. *)
  tmMkDefinition "repr_derive"%bs instance.
  
(*Instance repr_bool : Repr bool :=
{ repr_doc b := if b then str "true" else str "false" }.

Inductive bool_option := 
  | B1 : bool_option
  | B2 : bool -> bool_option.

Inductive myind (A B : Type) : Type := 
  | MyConstr : bool -> A -> B -> myind A B.
  
Definition bool_ind := {|
  inductive_mind :=
    (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "bool"%bs);
  inductive_ind := 0
|}.
Definition option_ind := {|
  inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "option"%bs);
  inductive_ind := 0
|}.
Definition boption_ind := {|
  inductive_mind := (MPfile ["Deriving"%bs], "bool_option"%bs);
  inductive_ind := 0
|}.
Definition myind_ := {|
  inductive_mind := (MPfile ["Deriving"%bs], "myind"%bs);
  inductive_ind := 0
|}.

Search "evar".

MetaCoq Run (derive myind_).
Print repr_derive.


MetaCoq Quote Definition rd := @repr_doc.
MetaCoq Quote Definition b := bool.



MetaCoq Test Unquote (tApp rd [b; tEvar fresh_evar_id []]).

Check (@repr_doc bool _).

MetaCoq Test Unquote 
  (tLambda 
    {| binder_name := nAnon ; binder_relevance := Relevant |}
    t_nat 
    (tEvar fresh_evar_id [tRel 0])).



(*Record color := { red : list nat * list nat ; green : list nat ; blue : list nat }. 

Instance reprColor : Repr color := 
{
  repr_doc c :=
    let fields := 
      [ ("red"  , repr_doc c.(red))
      ; ("green", repr_doc c.(green))
      ; ("blue" , repr_doc c.(blue))]
    in
    (* Pretty-print each field. *)
    let fields :=
      List.map (fun '(name, doc) => group (prefix 1 2 (str name ^^ str " :=") doc)) fields
    in
    (* Concatenate the fields (with semicolons). *)
    let contents := separate (str " ;" ^^ break 1) fields (*^^ ifflat empty (str " ;")*) in
    (* Add the leading and trailing brackets. *)
    let res := infix 1 2 (str "{|") contents (str "|}") in
    group (align res)
}.


Definition c_small := {| red := (range 2, range 0) ; green := range 3 ; blue := range 2 |}.
Definition c_large := {| red := (range 42, range 42) ; green := range 6 ; blue := range 2 |}.

Eval compute in repr c_small.
Eval compute in repr c_large.

Check 
{|
  red :=
    ([42; 41; 40; 39; 38; 37; 36; 35; 34; 33; 32; 31; 30; 29; 28; 27; 26; 25; 24;
      23; 22; 21; 20; 19; 18; 17; 16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5; 4;
      3; 2; 1],
     [42; 41; 40; 39; 38; 37; 36; 35; 34; 33; 32; 31; 30; 29; 28; 27; 26; 25; 24;
      23; 22; 21; 20; 19; 18; 17; 16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5; 4;
      3; 2; 1]) ;
  green := [6; 5; 4; 3; 2; 1] ;
  blue := [2; 1] ;
|}.

Eval compute in repr (range 42, List.map string_of_nat (range 26)).

Eval compute in String "034" "Hello".*)*)