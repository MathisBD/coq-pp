From Coq Require Import PrimString.
From MetaCoq.Template Require Import All.
From Repr Require Import All Utils.

Unset MetaCoq Strict Unquote Universe Mode.

(* Instances *)

Instance repr_bytestring : Repr bytestring.string := 
{ repr_doc _ s := group $ bracket """" (str $ pstring_of_bytestring s) """" }.

Instance repr_sort : Repr sort :=
{ repr_doc _ _ := str "#sort" }.

MetaCoq Run (derive_global cast_kind).
MetaCoq Run (derive_global name).
MetaCoq Run (derive_global modpath).

(* Testing *)

(* TODO : 
   1. handle records (it cannot be a fixpoint). 
   2. handle abbreviations of inductives (+ better error messages). *)

Definition x : ident := "x"%bs.
Eval compute in repr x.

(*Inductive term : Type :=
  |	tRel : nat -> term
  | tVar : ident -> term
  | tEvar : nat -> list term -> term
  | tSort : sort -> term
  | tCast : term -> cast_kind -> term -> term
  | tProd : aname -> term -> term -> term
  | tLambda : aname -> term -> term -> term
  | tLetIn : aname -> term -> term -> term -> term
  | tApp : term -> list term -> term
  | tConst : kername -> Instance.t -> term
  | tInd : inductive -> Instance.t -> term
  | tConstruct : inductive -> nat -> Instance.t -> term
  | tCase : case_info -> predicate term -> term -> list (branch term) -> term
  | tProj : projection -> term -> term
  | tFix : mfixpoint term -> nat -> term
  | tCoFix : mfixpoint term -> nat -> term
  | tInt : PrimInt63.int -> term
  | tFloat : PrimFloat.float -> term
  | tString : pstring -> term
  | tArray : Level.t -> list term -> term -> term -> term.
*)*)

(*
(** SCRATCH *)


Instance repr_nat : Repr nat :=
{ repr_doc _ n := str $ pstring_of_nat n }.

Instance repr_list {A} `{Repr A} : Repr (list A) :=
{
  repr_doc _ l := 
    let contents := flow_map (str ";" ^^ break 1) (repr_doc 0) l in
    group $ bracket "[" contents "]"
}.

Monomorphic Inductive vec A : nat -> Type :=
  | VNil : vec A 0
  | VCons : forall n, A -> vec A n -> vec A (S n).

Fixpoint repr_vec_test (A : Type) n (_ : Repr A) (prec : nat) (xs : vec A n) {struct xs} : doc unit :=
  let inst A' n' RA' := Build_Repr _ (repr_vec_test A' n' RA') in
  match xs with 
  | VNil => repr_ctor prec "VNil" []
  | VCons n x xs => repr_ctor prec "VCons" [repr_arg n; repr_arg x; repr_arg xs]
  end.

Monomorphic Inductive tree A : nat -> A -> Type :=
  | Leaf : forall a : A, tree A 0 a 
  | Node : forall a n m, A -> tree (list A) n [a] -> tree A m a -> tree A (n + m) a.
Arguments Leaf {A}.
Arguments Node {A}.
  
Definition repr_tree_test :=
  fix f 
    (A : Type) 
    (n : nat) (a : A) 
    (RA : Repr A) 
    (prec : nat) (xs : tree A n a) {struct xs} : doc unit :=
    let _ := fun (A' : Type) (n' : nat) (a' : A') (RA' : Repr A') => Build_Repr _ (f A' n' a' RA') in 
    match xs with 
    | Leaf a => repr_ctor prec "Leaf" [repr_arg a]
    | Node a n m x l r => repr_ctor prec "Node" [repr_arg a ; repr_arg n; repr_arg m ; repr_arg x; repr_arg l; repr_arg r]
    end.

(*Definition repr_tree' {A} {RA : Repr A} : Repr (tree A) := Build_Repr _ (repr_tree A RA).
Existing Instance repr_tree'.

Instance : Repr bool := { repr_doc b := if b then str "true" else str "false" }.

Eval compute in repr $ Node true (Node [true; false; true] Leaf Leaf) (Node false Leaf Leaf).*)

(** END SCRATCH *)*)
