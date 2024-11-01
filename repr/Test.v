From Coq Require Import PrimString Uint63 PrimFloat.
From MetaCoq.Template Require Import All.
From Repr Require Import All Utils.

Unset MetaCoq Strict Unquote Universe Mode.

(* Instances *)

Instance repr_bytestring : Repr bytestring.string := 
{ repr_prec _ s := group $ bracket """" (str $ pstring_of_bytestring s) """" }.

(*Instance repr_sort : Repr sort :=
{ repr_prec _ _ := str "#sort" }.*)

Instance repr_int63 : Repr int :=
{ repr_prec _ x := str $ pstring_of_nat $ to_nat x }.

Instance repr_float : Repr float :=
{ repr_prec _ _ := str "#float" }.

MetaCoq Run (derive_export cast_kind).
MetaCoq Run (derive_export name).
MetaCoq Run (derive_export relevance).
MetaCoq Run (derive_export binder_annot).
MetaCoq Run (derive_export modpath).
MetaCoq Run (derive_export Level.t_).
Instance repr_LevelExprSet_Raw_Ok {set} : Repr (LevelExprSet.Raw.Ok set) :=
{ repr_prec _ _ := str "_" }.

Instance repr_sort : Repr sort :=
{ repr_prec _ _ := str "#sort" }.

(*MetaCoq Run (derive_export LevelExprSet.t_).*)

MetaCoq Run (derive_export inductive).
MetaCoq Run (derive_export case_info).
MetaCoq Run (derive_export predicate).
MetaCoq Run (derive_export branch).
MetaCoq Run (derive_export def).
MetaCoq Run (derive_export projection).
MetaCoq Run (derive_export term).

(* A test on a mutual inductive. *)
Monomorphic Inductive mylist A := 
  | MyNil : mylist A 
  | MyCons : A -> mylist2 A -> mylist A
with mylist2 A :=
  | MyNil2 : mylist2 A 
  | MyCons2 : A -> mylist A -> mylist2 A.

MetaCoq Run (derive_export mylist).
