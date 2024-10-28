From MetaCoq.Template Require Import All.
From MetaCoq.Utils Require Import monad_utils.
Import MCMonadNotation.

Polymorphic Inductive plist A := 
  | PNil : plist A
  | PCons : A -> plist A -> plist A.

Polymorphic Definition pempty (A : Type) (xs : plist A) : bool := true.

MetaCoq Test Quote list.

Definition test : TemplateMonad unit :=
  mlet (env, _) <- tmQuoteRec list ;; 
  let ind := 
  {|
	  inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs]%list, "list"%bs);
    inductive_ind := 0
  |}
  in 
  let body := lookup_inductive env ind in
  tmPrint =<< tmEval cbv body.

MetaCoq Run test.