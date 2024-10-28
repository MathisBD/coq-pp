(** This file declares [Repr] instances for common types.
    
    In some cases we choose to not derive the instance automatically ;
    instead we provide a handcrafted instance that uses better syntax.
    For instance we print lists as "[1; 2; 3]" instead of the more verbose
    "cons 1 (cons 2 (cons 3 nil))".
*)

From Coq Require Import List String.
From PPrint Require Import All.
From Repr Require Import Class Utils Deriving.

Import ListNotations.
Open Scope string_scope.
Generalizable Variables A B C.

(** Representation of booleans. *)
(* DERIVE *)

(** Representation of natural numbers. *)
Instance repr_nat : Repr nat :=
{ repr_doc n := str $ string_of_nat n }.

(** Representation of strings. *)
Instance repr_string : Repr string :=
{ repr_doc s := group $ bracket """" (str s) """" }.

(** Representation of binary products. *)
Instance repr_prod `{Repr A} `{Repr B} : Repr (A * B) :=
{ 
  repr_doc '(a, b) := 
    let contents := repr_doc a ^^ str "," ^/^ repr_doc b in
    group $ paren contents
}.

(** Representation of lists. *)
Instance repr_list `{Repr A} : Repr (list A) :=
{
  repr_doc l := 
    let contents := flow_map (str ";" ^^ break 1) repr_doc l in
    group $ bracket "[" contents "]"
}.

(*Definition l n := List.init n id.
Eval compute in repr (l 42, List.combine (l 10) (l 10), l 3, l 25).*)
