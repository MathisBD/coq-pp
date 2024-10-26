From MetaCoq.Utils Require Import monad_utils MCList.
From MetaCoq.Template Require Import All.
From Coq Require Import Decimal String Ascii List.

Import ListNotations MCMonadNotation.
Open Scope string_scope.

Set Universe Polymorphism.

(** A convenient notation for function application, which saves many parentheses. *)
Notation "f $ x" := (f x) (at level 10, x at level 100, right associativity, only parsing).

(** [string_of_uint n] prints the uint [n] to a string in base 10. *)
Fixpoint string_of_uint (n : uint) :=
  match n with
  | Nil => ""
  | D0 n => String "0" (string_of_uint n)
  | D1 n => String "1" (string_of_uint n)
  | D2 n => String "2" (string_of_uint n)
  | D3 n => String "3" (string_of_uint n)
  | D4 n => String "4" (string_of_uint n)
  | D5 n => String "5" (string_of_uint n)
  | D6 n => String "6" (string_of_uint n)
  | D7 n => String "7" (string_of_uint n)
  | D8 n => String "8" (string_of_uint n)
  | D9 n => String "9" (string_of_uint n)
  end.

(** [string_of_nat n] prints the natural number [n] to a string in base 10. *)
Definition string_of_nat n : string :=
  string_of_uint (Nat.to_uint n).

(** [monad_mapi f l] is the same as [monad_map f l] except the function [f]
    is fed the index of each argument. *)
Definition monad_mapi (T : Type -> Type) (M : Monad T) (A B : Type) (f : nat -> A -> T B) (l : list A) :=
  let fix loop i l :=
    match l with
    | [] => ret []
    | x :: l => 
      mlet x' <- f i x ;;
      mlet l' <- loop (S i) l ;;
      ret (x' :: l')
    end
  in loop 0 l.

Arguments monad_mapi {T}%_function_scope {M} {A B}%_type_scope f%_function_scope l%_list_scope.

(** * List utility functions not present in Coq's stdlib. *)
Module List.
Include List.

(** [find_map pred l] applies [pred] to each element in [l] in order, 
    and returns the first result of the form [Some _]. *)
Fixpoint find_map {A B} (pred : A -> option B) (l : list A) : option B :=
  match l with 
  | [] => None
  | hd :: tl => 
    match pred hd with 
    | None => find_map pred tl
    | Some res => Some res
    end
  end.

(** [find_index pred l] returns the index of the first element in [l] 
    that satisfies the predicate [pred], or [None] if no such element exists. *)
Fixpoint find_index {A} (pred : A -> bool) (xs : list A) : option nat :=
  match xs with 
  | [] => None 
  | x :: xs => 
    if pred x then Some 0 else option_map S $ find_index pred xs
  end.

End List.

(** [ind_param_count ind_body] computes the number of parameters in the inductive [ind_body].
    This is a bit sketchy, in particular it might not be correct for mutual inductives. *)
Definition ind_param_count (ind_body : one_inductive_body) : nat :=
  (* Count the number of products in head position in [t]. *)
  let fix prod_count acc t :=
    match t with 
    | tProd _ _ t => prod_count (S acc) t
    | _ => acc
    end 
  in 
  prod_count 0 ind_body.(ind_type) - List.length ind_body.(ind_indices).

(** [iterate n f x] applies [f] [n] times to [x]. *)
Fixpoint iterate {A} (n : nat) (f : A -> A) (x : A) : A :=
  match n with 
  | 0 => x
  | S n => iterate n f (f x)
  end.

Definition map_def (f : term -> term) (d : def term) : def term :=
  {| dname := d.(dname) ; dtype := f d.(dtype) ; dbody := f d.(dbody) ; rarg := d.(rarg) |}.

Definition map_predicate (f : term -> term) (p : predicate term) : predicate term :=
  {| puinst := p.(puinst) 
  ;  pparams := List.map f p.(pparams) 
  ;  pcontext := p.(pcontext)
  ;  preturn := f p.(preturn) |}.

Definition map_branch (f : term -> term) (b : branch term) : branch term := 
  {| bcontext := b.(bcontext) ; bbody := f b.(bbody) |}.

(** [map_term f t] maps [f] on the immediate subterms of [t].
    It is not recursive and the order with which subterms are processed is not specified. *)
Definition map_term (f : term -> term) (t : term) : term := 
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => t
  | tEvar n ts => tEvar n (List.map f ts)
  | tCast b k t => tCast (f b) k (f t)
  | tProd name ty body => tProd name (f ty) (f body)
  | tLambda name ty body => tLambda name (f ty) (f body)
  | tLetIn name def ty body => tLetIn name (f def) (f ty) (f body)
  | tApp func args => tApp (f func) (List.map f args)
  | tProj proj t => tProj proj (f t)
  | tFix defs i => tFix (List.map (map_def f) defs) i
  | tCoFix defs i => tCoFix (List.map (map_def f) defs) i
  | tCase ci pred x branches => tCase ci (map_predicate f pred) (f x) (List.map (map_branch f) branches)
  | tArray l t def ty => tArray l (List.map f t) (f def) (f ty)
  end.

Definition map_decl (f : term -> term) (d : context_decl) : context_decl :=
  {| decl_name := d.(decl_name) ; decl_type := f d.(decl_type) ; decl_body := option_map f d.(decl_body) |}.

Definition map_predicate_with_binders {A} (lift : A -> A) (f : A -> term -> term) (acc : A) (p : predicate term) : predicate term :=
  let acc_return := iterate (List.length p.(pcontext)) lift acc in
  {| puinst := p.(puinst) 
  ;  pparams := List.map (f acc) p.(pparams) 
  ;  pcontext := p.(pcontext)
  ;  preturn := f acc_return p.(preturn) |}.

Definition map_branch_with_binders {A} (lift : A -> A) (f : A -> term -> term) (acc : A) (b : branch term) : branch term := 
  let acc_body := iterate (List.length b.(bcontext)) lift acc in
  {| bcontext := b.(bcontext) ; bbody := f acc_body b.(bbody) |}.

(** [map_term_with_binders lift f acc t] maps [f acc] on the immediate subterms of [t].
    It carries an extra data [acc] (typically a lift index) which is processed by [lift] 
    (which typically add 1 to [acc]) at each binder traversal.
    It is not recursive and the order with which subterms are processed is not specified. *)
Definition map_term_with_binders {A} (lift : A -> A) (f : A -> term -> term) (acc : A) (t : term) : term :=
  match t with
  | tRel _ | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ | tInt _ | tFloat _ | tString _ => t
  | tEvar n ts => tEvar n (List.map (f acc) ts)
  | tCast b k t => tCast (f acc b) k (f acc t)
  | tProd name ty body => tProd name (f acc ty) (f (lift acc) body)
  | tLambda name ty body => tLambda name (f acc ty) (f (lift acc) body)
  | tLetIn name def ty body => tLetIn name (f acc def) (f acc ty) (f (lift acc) body)
  | tApp func args => tApp (f acc func) (List.map (f acc) args)
  | tProj proj t => tProj proj (f acc t)
  (* For [tFix] and [tCoFix] we have to take care to lift the accumulator 
     only when processing the body of the (co)fixpoint. *)
  | tFix defs i => 
    let acc_body := iterate (List.length defs) lift acc in
    let map_def d := 
      {| dname := d.(dname) ; dtype := f acc d.(dtype) ; dbody := f acc_body d.(dbody) ; rarg := d.(rarg) |}
    in
    tFix (List.map map_def defs) i
  | tCoFix defs i => 
    let acc_body := iterate (List.length defs) lift acc in
    let map_def d := 
      {| dname := d.(dname) ; dtype := f acc d.(dtype) ; dbody := f acc_body d.(dbody) ; rarg := d.(rarg) |}
    in
    tCoFix (List.map map_def defs) i
  | tCase ci pred x branches => 
    tCase ci (map_predicate_with_binders lift f acc pred) (f acc x) (List.map (map_branch_with_binders lift f acc) branches)
  | tArray l t def ty => tArray l (List.map (f acc) t) (f acc def) (f acc ty)
  end.

Definition map_context_with_binders {A} (lift : A -> A) (f : A -> term -> term) (acc : A) (ctx : context) : context :=
  let n := List.length ctx in
  mapi (fun i decl => map_decl (f $ iterate (n - 1 - i) lift acc) decl) ctx.

(** [abstract [id_0; ...; id_n] k t] replaces [tVar id_i] by [tRel (k + i)] in [t] (for i <= n). 
    This is used to implement localy nameless. *)
Fixpoint abstract (ids : list ident) (k : nat) (t : term) : term := 
  match t with 
  | tVar id => 
    match List.find_index (String.eqb id) ids with 
    | None => t
    | Some i => tRel (k + i)
    end
  | _ => map_term_with_binders S (abstract ids) k t
  end.

(** Specialization of [abstract] to [k = 0]. *)
Definition abstract0 ids t := abstract ids 0 t.

(** [instantiate [id_0; ...; id_n] k t] replaces [tRel (k + i)] by [tVar id_i] in [t] (for i <= n). 
    This is used to implement localy nameless. *)
Definition instantiate (ids : list ident) (k : nat) (t : term) : term := 
  subst (List.map tVar ids) k t.

(** Specialization of [instantiate] to [k = 0]. *)
Definition instantiate0 ids t := instantiate ids 0 t.

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
