(** This file implements a Coq command that automatically derives [Repr] instances
    for inductives and records. *)

From MetaCoq.Template Require Import All Pretty.
From MetaCoq.Utils Require Import monad_utils.
From Coq Require Import List String.
From PPrint Require Import All.
From Repr Require Import Class Utils LocallyNameless Class.

Import ListNotations MCMonadNotation.

(** TODO : this is for debugging. *)
Axiom evar_axiom : forall A, A.
MetaCoq Quote Definition quoted_evar_axiom := evar_axiom.

(** Pretty-print the application of constructor [label] to a list of arguments [args]. *)
Definition repr_ctor (label : string) (args : list (doc unit)) : doc unit :=
  (*let res := separate (break 1) (str label :: args) in*)
  let res := flow (break 1) (str label :: args) in
  group (hang 4 res).

(** SCRATCH *)

Instance repr_list {A} `{Repr A} : Repr (list A) :=
{
  repr_doc l := 
    let contents := flow_map (str ";" ^^ break 1) repr_doc l in
    let res := str "[" ^^ align contents ^^ str "]" in
    group (align res)
}.

Instance repr_nat : Repr nat.
Admitted.

Inductive vec A : nat -> Type :=
  | VNil : vec A 0
  | VCons : forall n, A -> vec A n -> vec A (S n).

Fixpoint repr_vec (A : Type) (_ : Repr A) n (xs : vec A n) {struct xs} : doc unit :=
  let inst A' RA' n' := Build_Repr _ (repr_vec A' RA' n') in
  match xs with 
  | VNil => repr_ctor "VNil" []
  | VCons n x xs => repr_ctor "VCons" [repr_doc n; repr_doc x; repr_doc xs]
  end.

Inductive tree A : nat -> Type :=
  | Leaf : tree A 0 
  | Node : forall n m, A -> tree (list A) n -> tree A m -> tree A (n + m).
Arguments Leaf {A}.
Arguments Node {A}.
  
Definition repr_tree :=
  fix f (A : Type) (RA : Repr A) (n : nat) (xs : tree A n) {struct xs} : doc unit :=
    let _ := fun (A' : Type) (RA' : Repr A') (n' : nat) => Build_Repr _ (f A' RA' n') in 
    match xs with 
    | Leaf => repr_ctor "Leaf" []
    | Node n m x l r => repr_ctor "Node" [repr_doc n; repr_doc m ; repr_doc x; repr_doc l; repr_doc r]
    end.

(*Definition repr_tree' {A} {RA : Repr A} : Repr (tree A) := Build_Repr _ (repr_tree A RA).
Existing Instance repr_tree'.

Instance : Repr bool := { repr_doc b := if b then str "true" else str "false" }.

Eval compute in repr $ Node true (Node [true; false; true] Leaf Leaf) (Node false Leaf Leaf).*)

(** END SCRATCH *)

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

(** [with_params_and_reprs ctx ind ind_body k] calls the continuation [k] 
    with an extended context which contains :
    - declarations for the parameters of the inductive [ind].
    - declarations for instances of [Repr] for each parameter.

    This is a common pattern that is reused several times below. *)
Definition with_params_and_reprs {T} ctx (ind : inductive) (ind_body : one_inductive_body) 
  (k : NamedCtx.t -> list ident -> list ident -> T) : T :=
  (* Declare the inductive parameters. *)
  with_ind_params ctx ind_body $ fun ctx params =>
  (* Declare a Repr instance for each parameter. *)
  let repr_decls := List.map (fun p => mk_decl "H"%bs $ mkApp quoted_Repr $ tVar p) params in
  with_decls ctx repr_decls $ fun ctx param_insts =>
    (* Call the continuation. *)
    k ctx params param_insts.

(** Build a single argument. *)
Definition build_arg ctx (arg : ident) : term :=
  (* I use an evar in place of the [Repr] instance, which will be solved when unquoting the term. *)
  (*let evar := fresh_evar ctx in*)
  let evar := mkApp quoted_evar_axiom $ mkApp quoted_Repr $ NamedCtx.get_type ctx arg in
  ret $ mkApps quoted_repr_doc [NamedCtx.get_type ctx arg; evar; tVar arg].

(** Build a branch for a single constructor. *)
Definition build_branch ctx (ind : inductive) (params : list term) (ctor_body : constructor_body) (quoted_ctor_name : term) : branch term :=
  (* Get the list of arguments of the constructor. *)
  with_ctor_args ctx ind ctor_body params $ fun ctx args =>
  (* Apply [repr_ctor] to the label and the arguments. *)
  let repr_args := term_list quoted_doc_unit $ List.map (build_arg ctx) args in
  mk_branch ctx args $ mkApps quoted_repr_ctor [quoted_ctor_name; repr_args].

(* fun (A' : Type) (H' : Repr A') => Build_Repr (mylist A') (fix_param A' H') *)

(** Bind the recursive [Repr] instance. *)
Definition with_rec_inst {T} ctx (ind : inductive) (ind_body : one_inductive_body) (fix_param : term) (k : NamedCtx.t -> ident -> T) : T :=
  let (ty, body) := 
    with_params_and_reprs ctx ind ind_body $ fun ctx params param_insts =>
    let ind_params := mkApps (tInd ind []) $ List.map tVar params in
    let body := mkApps fix_param $ List.map tVar $ List.app params param_insts in
    ( mk_prods ctx (List.app params param_insts) $ mkApp quoted_Repr ind_params
    , mk_lambdas ctx (List.app params param_insts) $ mkApps quoted_Build_Repr [ind_params ; body])
  in 
  let decl := 
    {| decl_name := {| binder_name := nNamed "rec_inst"%bs ; binder_relevance := Relevant |}
    ;  decl_type := ty
    ;  decl_body := Some body |}
  in
  with_decl ctx decl k.

(** Build the case expression. *)
Definition build_match ctx (ind : inductive) (ind_body : one_inductive_body) 
  (params : list term) (x : term) (ctor_names : list term) : term :=
  (* Case info. *)  
  let ci := {| ci_ind := ind ; ci_npar := List.length params ; ci_relevance := Relevant |} in
  (* Case predicate. *)
  let pred := 
    with_ind_indices ctx ind_body params $ fun ctx indices =>
    with_decl ctx (mk_decl "x"%bs $ mkApps (tInd ind []) params) $ fun ctx x => 
      mk_pred ctx params indices x quoted_doc_unit
  in
  (* Case branches. *)
  let branches := map2 (build_branch ctx ind params) ind_body.(ind_ctors) ctor_names in
  (* Result. *)
  tCase ci pred x branches.

(** Build the raw function's type. *)
Definition build_func_ty ctx (ind : inductive) (ind_body : one_inductive_body) : term :=
  with_params_and_reprs ctx ind ind_body $ fun ctx params param_insts =>
  (* Declare the inductive element. *)
  with_decl ctx (mk_decl "x"%bs $ mkApps (tInd ind []) $ List.map tVar params) $ fun ctx x =>
  (* Make the final product. *)
  mk_prods ctx (List.concat [params; param_insts; [x]]) quoted_doc_unit.

(* TODO : this is for debugging. *)
Definition second (A : Type) (x : A) (y : doc unit) := y.
MetaCoq Quote Definition quoted_second := second. 

(** Build the raw function. *)
Definition build_func ctx (ind : inductive) (ind_body : one_inductive_body) (ctor_names : list term) : term :=
  (* Declare the fixpoint parameter. *)
  with_decl ctx (mk_decl "fix_param"%bs $ build_func_ty ctx ind ind_body) $ fun ctx fix_param =>
  with_params_and_reprs ctx ind ind_body $ fun ctx params param_insts =>
  (* Declare the input parameter [x]. *)
  with_decl ctx (mk_decl "x"%bs $ mkApps (tInd ind []) $ List.map tVar params) $ fun ctx x =>  
  (* Add a let-binding for the recursive [Repr] instance. *)
  with_rec_inst ctx ind ind_body (tVar fix_param) $ fun ctx rec_inst =>
  (* Build the match. *)
  let body := build_match ctx ind ind_body (List.map tVar params) (tVar x) ctor_names in
  (* Package it in a [Repr] record. *)
  (*let record := mkApps quoted_Build_Repr [mkApps (tInd ind []) $ List.map tVar params; f] in*)
  (* Abstract over all the variables. *)
  let vars := List.concat [params; param_insts; [x]] in
  mk_fix ctx fix_param (List.length params + List.length param_insts) $ 
    mk_lambdas ctx vars $ 
      mk_lets ctx [rec_inst] $ 
        (* This is a hack : for some reason without this the let-in gets reduced when adding the 
         definition to the global environment.
         In the future we will return only [body]. *)
        mkApps quoted_second [NamedCtx.get_type ctx rec_inst ; tVar rec_inst ; body].

(** Derive command entry-point. *)
Definition derive (ind : inductive) : TemplateMonad unit :=
  (* Get the global environment needed to type the inductive. *)
  mlet t_doc <- tmQuote doc ;;
  mlet t_unit <- tmQuote unit ;;
  mlet env <- env_of_terms [tInd ind []; t_unit ; t_doc; quoted_Repr] ;;
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
  let instance := build_func NamedCtx.empty ind ind_body ctor_names in
  tmPrint "FUNC_TY" ;;
  tmPrint =<< tmEval cbv (build_func_ty NamedCtx.empty ind ind_body) ;;
  tmPrint "FUNC" ;;
  tmPrint =<< tmEval cbv instance ;;
  tmPrint =<< tmEval cbv (print_term (env, Monomorphic_ctx) [] true instance) ;;
  (* Add the instance to the global environment and register it as an instance. *)
  tmMkDefinition "repr_derive"%bs instance.
  
(** TESTING *)

Instance repr_bool : Repr bool :=
{ repr_doc b := if b then str "true" else str "false" }.

Inductive bool_option := 
  | B1 : bool_option
  | B2 : bool -> bool_option.

Inductive mylist (A : Type) :=
  | MyNil : mylist A
  | MyCons : A -> mylist A -> mylist A.

Inductive myind (A B : Type) : Type := 
  | MyConstr : bool -> A -> myind A bool -> myind A B.
  
Definition bool_ind_ := {|
  inductive_mind :=
    (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "bool"%bs);
  inductive_ind := 0
|}.
Definition boption_ind_ := {|
  inductive_mind := (MPfile ["Deriving"%bs], "bool_option"%bs);
  inductive_ind := 0
|}.
Definition option_ind_ := {|
  inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "option"%bs);
  inductive_ind := 0
|}.
Definition mylist_ind_ := {|
inductive_mind :=
    (MPfile ["Deriving"%bs], "mylist"%bs);
  inductive_ind := 0
|}.
Definition myind_ind_ := {|
  inductive_mind := (MPfile ["Deriving"%bs], "myind"%bs);
  inductive_ind := 0
|}.

MetaCoq Run (derive myind_ind_).
Print repr_derive.

Definition x := (fix fix_param
(A B : Type) (H : Repr A) (H0 : Repr B) (x : myind A B) {struct x} :
doc unit :=
let _ :=(fun (A0 B0 : Type) (H1 : Repr A0) (H2 : Repr B0) =>
   {| repr_doc := fix_param A0 B0 H1 H2 |})
   in
  match x with
  | @MyConstr _ _ x0 x1 x2 =>
      repr_ctor "MyConstr" [repr_doc x0; repr_doc x1; repr_doc x2]
  end).

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