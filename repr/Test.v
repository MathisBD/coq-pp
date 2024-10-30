From Coq Require Import PrimString Uint63 PrimFloat.
From MetaCoq.Template Require Import All.
From Repr Require Import All Utils.

(*Unset MetaCoq Strict Unquote Universe Mode.

(* Instances *)

Instance repr_bytestring : Repr bytestring.string := 
{ repr_doc _ s := group $ bracket """" (str $ pstring_of_bytestring s) """" }.

Instance repr_sort : Repr sort :=
{ repr_doc _ _ := str "#sort" }.

Instance repr_int63 : Repr int :=
{ repr_doc _ x := str $ pstring_of_nat $ to_nat x }.

Instance repr_float : Repr float :=
{ repr_doc _ _ := str "#float" }.

MetaCoq Run (derive_global cast_kind).
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

MetaCoq Run (derive_global term).


MetaCoq Quote Definition big_def := 
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
  
Time Eval compute in repr big_def.


(* Testing *)

(* TODO : 
   1. handle abbreviations of inductives (+ better error messages).
   2. why is this slow ? 
      MetaCoq Run (derive_global mfixpoint).
      >> "Not and inductive" 
*)

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
