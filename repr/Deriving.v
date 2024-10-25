(** This file implements a Coq command that automatically derives [Repr] instances
    for inductives and records. *)

From MetaCoq.Template Require Import All Pretty.
From MetaCoq.Utils Require Import monad_utils.
From Coq Require Import List String.
From PPrint Require Import All.
From Repr Require Import Class Utils LocallyNameless Class.

Import ListNotations MCMonadNotation.

Inductive level : Type :=
  | Infinity : level
  | ExtremelyLongName : nat -> list nat -> nat -> list nat -> level
  | Under : list nat * list nat -> level.

(*
Definition repr_doc_nat : nat -> doc unit :=
  fun n => str (string_of_nat n).
Definition inst := {| repr_doc := repr_doc_nat |}.
Existing Instance inst.
*)

(** Metacoq terms corresponding to [nil] and [cons]. *)
MetaCoq Quote Definition quoted_nil := (@nil).
MetaCoq Quote Definition quoted_cons := (@cons).

(** [term_list ty xs] builds the term corresponding to the list [x1; ...; xn], 
    assuming each [xi] has type [ty]. *)
Fixpoint term_list (ty : term) (xs : list term) : term :=
  match xs with 
  | [] => mkApp quoted_nil ty
  | x :: xs => mkApps quoted_cons [ty; x; term_list ty xs]
  end.

(** Apply the constructor named [label] to a list of arguments [args]. *)
Definition repr_ctor (label : string) (args : list (doc unit)) : doc unit :=
  (*let res := separate (break 1) (str label :: args) in*)
  let res := flow (break 1) (str label :: args) in
  group (hang 4 res).

(*MetaCoq Quote Definition repr_list := (fun (x : nat) (y : list nat) => _).*)
(*    (fun l => match l with 
    | Infinity => repr_ctor "" []
    | ExtremelyLongName n ns m ms => repr_ctor "" [@repr_doc _ _ n; repr_doc ns; repr_doc m ; repr_doc ms]
    | Under x => repr_ctor "" [repr_doc x]
    end).*)

(*MetaCoq Run (
  tmBind 
    (tmInferInstance None (Repr nat)) 
    (fun x => tmPrint x)).*)

(** Build a single argument. *)
Definition build_arg ctx (arg : ident) : TemplateMonad term :=
  (* Get the type of the argument. *)
  let arg_ty := NamedCtx.get_type ctx arg in
  mlet t_arg_ty <- tmUnquoteTyped Type arg_ty ;;
  (* Get the corresponding [Repr] instance. This only works if the argument type is closed. *)
  mlet t_inst <- tmInferInstance None (Repr t_arg_ty) ;;
  match t_inst with
  | my_None => tmFail "Could not infer Repr instance on constructor argument"%bs
  | my_Some t_inst => 
    mlet inst <- tmQuote t_inst ;; 
    mlet rd <- tmQuote (@repr_doc) ;;
    ret $ mkApps rd [arg_ty; inst; tVar arg]
  end.

(** Build a branch for a single constructor. *)
Definition build_branch ctx (params : list term) (ctor_body : constructor_body) : TemplateMonad (branch term) :=
  (* Get the label of the constructor. *)
  mlet label <- tmQuote =<< tmEval cbv (bytestring.String.to_string ctor_body.(cstr_name)) ;;
  (* Get the list of arguments of the constructor. *)
  with_ctor_args ctx ctor_body params $ fun ctx args =>
    mlet repr_args <- monad_map (build_arg ctx) args ;;
    (* Apply [repr_ctor] to the label and the arguments. *)
    mlet rc <- tmQuote repr_ctor ;;
    mlet doc_unit <- tmQuote (doc unit) ;;
    ret $ mk_branch ctx args $ mkApps rc [label; term_list doc_unit repr_args].

(** Derive the [repr_doc] function for an inductive type. *)
Definition build_func ctx (ind : inductive) (ind_body : one_inductive_body) (params : list term) : TemplateMonad term :=
  (* Declare the input parameter [x]. *)
  with_decl ctx (mk_decl "x"%bs $ mkApps (tInd ind []) params) $ fun ctx x =>  
  (* Case info. *)  
  let ci := {| ci_ind := ind ; ci_npar := List.length params ; ci_relevance := Relevant |} in
  (* Case predicate. *)
  mlet doc_unit <- tmQuote (doc unit) ;;
  let pred := 
    with_ind_indices ctx ind_body params $ fun ctx indices =>
    with_decl ctx (mk_decl "x"%bs $ mkApps (tInd ind []) params) $ fun ctx x => 
      mk_pred ctx params indices x doc_unit
  in
  tmPrint =<< tmEval cbv pred ;;
  (* Case branches. *)
  mlet branches <- monad_map (build_branch ctx params) ind_body.(ind_ctors) ;;
  (* Bind the input parameter. *)
  ret (mk_lambda ctx x $ tCase ci pred (tVar x) branches).

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
  (* Derive the [repr_doc] function. *)
  mlet func <- build_func NamedCtx.empty ind ind_body [] ;;
  tmPrint =<< tmEval cbv (print_term (env, Monomorphic_ctx) [] true func) ;;
  (* Package it in a [Repr] intance. *)
  let repr_ind := {| inductive_mind := (MPfile ["Class"%bs ; "Repr"%bs], "Repr"%bs); inductive_ind := 0 |} in
  let instance := mkApps (tConstruct repr_ind 0 []) [tInd ind []; func] in
  (* Add the instance to the global environment. *)
  tmMkDefinition "repr_boption"%bs instance.
  
Instance repr_bool : Repr bool :=
{ repr_doc b := if b then str "true" else str "false" }.

Inductive bool_option := 
  | BNone : bool_option
  | BSome : bool -> bool_option.

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

(*MetaCoq Test Quote (fun x =>
  match b with 
  | true => str "true"
  | false => str "false"
  end).*)

MetaCoq Run (derive boption_ind).
Print repr_boption.
Existing Instance repr_bool.

Eval compute in repr true.


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

Fixpoint range n : list nat := 
  match n with 
  | 0 => []
  | S n => S n :: range n
  end.

Inductive level : Type :=
  | Infinity : level
  | ExtremelyLongName : nat -> list nat -> nat -> list nat -> level
  | Under : list nat * list nat -> level.

Definition repr_constr (label : string) (args : list (doc unit)) : doc unit :=
  (*let res := separate (break 1) (str label :: args) in*)
  let res := flow (break 1) (str label :: args) in
  group (hang 4 res).
  
Instance reprLevel : Repr level :=
{
  repr_doc l := 
    match l with 
    | Infinity => repr_constr "Infinity" []
    | ExtremelyLongName n ns m ms => repr_constr "ExtremelyLongName" [repr_doc n; repr_doc ns; repr_doc m ; repr_doc ms]
    | Under x => repr_constr "Under" [repr_doc x]
    end
}.

Definition l_small := ExtremelyLongName 4 [42; 41] 0 [].
Definition l_large := ExtremelyLongName 42 (range 42) 0 (range 25).

Eval compute in l_large.

Eval compute in repr l_large.

Check 
ExtremelyLongName 42
  [42; 41; 40; 39; 38; 37; 36; 35; 34; 33; 32; 31; 30; 29; 28; 27; 26; 25; 24;
   23; 22; 21; 20; 19; 18; 17; 16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5; 4; 3;
   2; 1] 0
  [25; 24; 23; 22; 21; 20; 19; 18; 17; 16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5;
   4; 3; 2; 1].

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