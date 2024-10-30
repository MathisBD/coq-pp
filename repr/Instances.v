(** This file declares [Repr] instances for common types.
    
    In some cases we choose to not derive the instance automatically ;
    instead we provide a handcrafted instance that uses better syntax.
    For instance we print lists as "[1; 2; 3]" instead of the more verbose
    "cons 1 (cons 2 (cons 3 nil))".
*)

From Coq Require Import List PrimString String.
From PPrint Require Import All.
From Repr Require Import Class Utils Deriving.

Import ListNotations.
Open Scope string_scope.
Generalizable Variables A B C.

(* This option is required to use the [derive] command.
   TODO : figure out how to hide it. *)
Unset MetaCoq Strict Unquote Universe Mode.

(** Helper function which adds parentheses around an application if needed. *)
Definition paren_app (min_prec : nat) (app_doc : doc unit) : doc unit :=
  if Nat.ltb 0 min_prec then paren app_doc else app_doc.

(** * Custom Instances. *)

Instance repr_nat : Repr nat :=
{ repr_doc _ n := str $ pstring_of_nat n }.

Instance repr_pstring : Repr PrimString.string :=
{ repr_doc _ s := group $ bracket """" (str s) """" }.

Instance repr_string : Repr String.string :=
{ repr_doc _ s := group $ bracket """" (str $ pstring_of_string s) """" }.

Instance repr_prod `{Repr A} `{Repr B} : Repr (A * B) :=
{ 
  repr_doc _ '(a, b) := 
    let contents := repr_doc 0 a ^^ str "," ^/^ repr_doc 0 b in
    group $ paren contents
}.

Instance repr_list `{Repr A} : Repr (list A) :=
{
  repr_doc _ l := 
    let contents := flow_map (str ";" ^^ break 1) (repr_doc 0) l in
    group $ bracket "[" contents "]"
}.

(** * Derived Instances. *)

MetaCoq Run (derive_global bool).
MetaCoq Run (derive_global option).
MetaCoq Run (derive_global sum).

(*Time Eval compute in repr (inr ([3; 4; 3; 42], [inl (true)])).

Inductive expr := 
  | ENat : nat -> expr 
  | EAdd : expr -> expr -> expr
  | EMul : expr -> expr -> expr.
MetaCoq Run (derive_global expr).

Definition n := ENat 0.
Definition e x := EMul x (EMul x (EAdd x n)).
Time Eval compute in e $ e $ e $ e $ e n.
Time Eval compute in repr (e $ e $ e $ e $ e n).

Instance repr_expr : Repr expr :=
{
  repr_doc := fix f min_prec e :=
    match e with 
    | ENat n => repr_doc 0 n 
    | EAdd e1 e2 => 
      let prec := 10 in
      let contents := f prec e1 ^+^ str "+" ^+^ f (S prec) e2 in
      paren_if min_prec prec contents
    | EMul e1 e2 => 
      let prec := 20 in 
      let contents := f prec e1 ^+^ str "*" ^+^ f (S prec) e2 in
      paren_if min_prec prec contents
    end
}.


Definition l n := List.init n id.
Eval compute in repr (l 42, List.combine (l 10) (l 10), l 3, l 25).
*)