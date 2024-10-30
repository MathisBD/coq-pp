From Coq Require Import PrimString Uint63 PrimFloat.
From MetaCoq.Template Require Import All.
From Repr Require Import All Utils.

Unset MetaCoq Strict Unquote Universe Mode.

(* Instances *)

Instance repr_bytestring : Repr bytestring.string := 
{ repr_prec _ s := group $ bracket """" (str $ pstring_of_bytestring s) """" }.

Instance repr_sort : Repr sort :=
{ repr_prec _ _ := str "#sort" }.

Instance repr_int63 : Repr int :=
{ repr_prec _ x := str $ pstring_of_nat $ to_nat x }.

Instance repr_float : Repr float :=
{ repr_prec _ _ := str "#float" }.

(*MetaCoq Run (derive_global cast_kind).
MetaCoq Run (derive_global name).
MetaCoq Run (derive_global relevance).
MetaCoq Run (derive_global binder_annot).
MetaCoq Run (derive_global modpath).
MetaCoq Run (derive_global Level.t_).
MetaCoq Run (derive_global inductive).
MetaCoq Run (derive_global case_info).
MetaCoq Run (derive_global predicate).
MetaCoq Run (derive_global branch).
MetaCoq Run (derive_global def).
MetaCoq Run (derive_global projection).

MetaCoq Run (derive_global term).*)


(*MetaCoq Quote Definition big_def := 
(fun (Ann : Type) (M : Type -> Type) (MonadM : Monad.Monad M)
(MonadPPrintM : MonadPPrint Ann M) =>
fix prettyM
(doc : doc Ann) (flat : bool) (width indent col : nat) {struct doc} :
M nat :=
match doc with
| Empty => Monad.ret col
| Blank n =>
    Monad.bind (add_string (make (of_nat n) " "))
      (fun _ : unit => Monad.ret (col + n))
| Str len s =>
    Monad.bind (add_string s) (fun _ : unit => Monad.ret (col + len))
| IfFlat _ doc1 doc2 =>
    prettyM (if flat then doc1 else doc2) flat width indent col
| HardLine =>
    Monad.bind (add_string (make 1 10%uint63))
      (fun _ : unit =>
       Monad.bind (add_string (make (of_nat indent) " "))
         (fun _ : unit => Monad.ret indent))
| Cat _ doc1 doc2 =>
    Monad.bind (prettyM doc1 flat width indent col)
      (fun col0 : nat => prettyM doc2 flat width indent col0)
| Nest _ n doc0 => prettyM doc0 flat width (indent + n) col
| Group req doc0 =>
    let doc_flat :=
      match req with
      | Infinity => false
      | Width req0 => Nat.leb (col + req0) width
      end in
    prettyM doc0 (flat || doc_flat)%bool width indent col
| Align _ doc0 => prettyM doc0 flat width col col
| Annot _ ann doc0 =>
    Monad.bind (enter_annot ann)
      (fun _ : unit =>
       Monad.bind (prettyM doc0 flat width indent col)
         (fun col0 : nat =>
          Monad.bind (exit_annot ann) (fun _ : unit => Monad.ret col0)))
end).
  
Time Eval compute in repr big_def.*)

(* TODO : 
   1. handle abbreviations of inductives (+ better error messages).
   2. why is this slow ? 
      MetaCoq Run (derive_global mfixpoint).
      >> "Not and inductive" 
*)