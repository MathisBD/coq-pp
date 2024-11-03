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

(********************************************************)

MetaCoq Quote Definition big_def := 
(fun (A : Type) (H : Repr A) =>
{|
  repr_prec :=
	(fix fix_mylist
       (A0 : Type) (H0 : Repr A0) (min_prec : nat) (x : mylist A0) {struct x} :
         doc unit :=
       match x with
       | @MyNil _ => repr_ctor min_prec "MyNil" []
       | @MyCons _ x0 x1 =>
           repr_ctor min_prec "MyCons" [repr_arg x0; repr_arg x1]
       end
     with fix_mylist2
       (A0 : Type) (H0 : Repr A0) (min_prec : nat) 
       (x : mylist2 A0) {struct x} : doc unit :=
       match x with
       | @MyNil2 _ => repr_ctor min_prec "MyNil2" []
       | @MyCons2 _ x0 x1 =>
           repr_ctor min_prec "MyCons2" [repr_arg x0; repr_arg x1]
       end
     for
     fix_mylist) A H
|}).

Print big_def.

MetaCoq Quote Definition huge_def := (tLambda {| binder_name := nNamed "A"%bs; binder_relevance := Relevant |}
(tSort (sType (Universe.make' (Level.level "Test.218"%bs))))
(tLambda {| binder_name := nNamed "H"%bs; binder_relevance := Relevant |}
 (tApp
      (tInd
         {|
           inductive_mind := (MPfile ["Class"%bs; "Repr"%bs], "Repr"%bs);
           inductive_ind := 0
         |} []) [tRel 0])
   (tApp
      (tConstruct
         {|
           inductive_mind := (MPfile ["Class"%bs; "Repr"%bs], "Repr"%bs);
           inductive_ind := 0
         |} 0 [])
      [tApp
         (tInd
            {|
              inductive_mind := (MPfile ["Test"%bs], "mylist"%bs);
              inductive_ind := 0
            |} []) [tRel 1];
       tApp
         (tFix
            [{|
               dname :=
                 {|
                   binder_name := nNamed "fix_mylist"%bs;
                   binder_relevance := Relevant
                 |};
               dtype :=
                 tProd
                   {|
                     binder_name := nNamed "A0"%bs;
                     binder_relevance := Relevant
                   |}
                   (tSort
                      (sType (Universe.make' (Level.level "Test.219"%bs))))
                   (tProd
                      {|
                        binder_name := nNamed "H0"%bs;
                        binder_relevance := Relevant
                      |}
                      (tApp
                         (tInd
                            {|
                              inductive_mind :=
                                (MPfile ["Class"%bs; "Repr"%bs], "Repr"%bs);
                              inductive_ind := 0
                            |} []) [tRel 0])
                      (tProd
                         {|
                           binder_name := nNamed "min_prec"%bs;
                           binder_relevance := Relevant
                         |}
                         (tInd
                            {|
                              inductive_mind :=
                                (MPfile
                                   ["Datatypes"%bs; "Init"%bs; "Coq"%bs],
                                 "nat"%bs);
                              inductive_ind := 0
                            |} [])
                         (tProd
                            {|
                              binder_name := nNamed "x"%bs;
                              binder_relevance := Relevant
                            |}
                            (tApp
                               (tInd
                                  {|
                                    inductive_mind :=
                                      (MPfile ["Test"%bs], "mylist"%bs);
                                    inductive_ind := 0
                                  |} []) [tRel 2])
                            (tApp
                               (tInd
                                  {|
                                    inductive_mind :=
                                      (MPfile ["Documents"%bs; "PPrint"%bs],
                                       "doc"%bs);
                                    inductive_ind := 0
                                  |} [])
                               [tInd
                                  {|
                                    inductive_mind :=
                                      (MPfile
                                         ["Datatypes"%bs; "Init"%bs;
                                          "Coq"%bs], "unit"%bs);
                                    inductive_ind := 0
                                  |} []]))));
               dbody :=
                 tLambda
                   {|
                     binder_name := nNamed "A0"%bs;
                     binder_relevance := Relevant
                   |}
                   (tSort
                      (sType (Universe.make' (Level.level "Test.219"%bs))))
                   (tLambda
                      {|
                        binder_name := nNamed "H0"%bs;
                        binder_relevance := Relevant
                      |}
                      (tApp
                         (tInd
                            {|
                              inductive_mind :=
                                (MPfile ["Class"%bs; "Repr"%bs], "Repr"%bs);
                              inductive_ind := 0
                            |} []) [tRel 0])
                      (tLambda
                         {|
                           binder_name := nNamed "min_prec"%bs;
                           binder_relevance := Relevant
                         |}
                         (tInd
                            {|
                              inductive_mind :=
                                (MPfile
                                   ["Datatypes"%bs; "Init"%bs; "Coq"%bs],
                                 "nat"%bs);
                              inductive_ind := 0
                            |} [])
                         (tLambda
                            {|
                              binder_name := nNamed "x"%bs;
                              binder_relevance := Relevant
                            |}
                            (tApp
                               (tInd
                                  {|
                                    inductive_mind :=
                                      (MPfile ["Test"%bs], "mylist"%bs);
                                    inductive_ind := 0
                                  |} []) [tRel 2])
                            (tCase
                               {|
                                 ci_ind :=
                                   {|
                                     inductive_mind :=
                                       (MPfile ["Test"%bs], "mylist"%bs);
                                     inductive_ind := 0
                                   |};
                                 ci_npar := 1;
                                 ci_relevance := Relevant
                               |}
                               {|
                                 puinst := [];
                                 pparams := [tRel 3];
                                 pcontext :=
                                   [{|
                                      binder_name := nNamed "x"%bs;
                                      binder_relevance := Relevant
                                    |}];
                                 preturn :=
                                   tApp
                                     (tInd
                                        {|
                                          inductive_mind :=
                                            (MPfile
                                               [
                                               "Documents"%bs; "PPrint"%bs],
                                             "doc"%bs);
                                          inductive_ind := 0
                                        |} [])
                                     [tInd
                                        {|
                                          inductive_mind :=
                                            (MPfile
                                               [
                                               "Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "unit"%bs);
                                          inductive_ind := 0
                                        |} []]
                               |} (tRel 0)
                               [{|
                                  bcontext := [];
                                  bbody :=
                                    tApp
                                      (tConst
                                         (MPfile ["Deriving"%bs; "Repr"%bs],
                                          "repr_ctor"%bs) [])
                                      [tRel 1; tString "MyNil";
                                       tApp
                                         (tConstruct
                                            {|
                                              inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "list"%bs);
                                              inductive_ind := 0
                                            |} 0 [])
                                         [tApp
                                            (tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Documents"%bs; "PPrint"%bs],
                                               "doc"%bs);
                                               inductive_ind := 0
                                               |} [])
                                            [tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "unit"%bs);
                                               inductive_ind := 0
                                               |} []]]]
                                |};
                                {|
                                  bcontext :=
                                    [{|
                                       binder_name := nNamed "x1"%bs;
                                       binder_relevance := Relevant
                                     |};
                                     {|
                                       binder_name := nNamed "x0"%bs;
                                       binder_relevance := Relevant
                                     |}];
                                  bbody :=
                                    tApp
                                      (tConst
                                         (MPfile ["Deriving"%bs; "Repr"%bs],
                                          "repr_ctor"%bs) [])
                                      [tRel 3; tString "MyCons";
                                       tApp
                                         (tConstruct
                                            {|
                                              inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "list"%bs);
                                              inductive_ind := 0
                                            |} 1 [])
                                         [tApp
                                            (tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Documents"%bs; "PPrint"%bs],
                                               "doc"%bs);
                                               inductive_ind := 0
                                               |} [])
                                            [tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "unit"%bs);
                                               inductive_ind := 0
                                               |} []];
                                          tApp
                                            (tConst
                                               (
                                               MPfile
                                               ["Deriving"%bs; "Repr"%bs],
                                               "repr_arg"%bs)
                                               [
                                               Level.level "Test.221"%bs])
                                            [tRel 5; tRel 4; tRel 1];
                                          tApp
                                            (tConstruct
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "list"%bs);
                                               inductive_ind := 0
                                               |} 1 [])
                                            [tApp
                                               (tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Documents"%bs; "PPrint"%bs],
                                               "doc"%bs);
                                               inductive_ind := 0
                                               |} [])
                                               [
                                               tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "unit"%bs);
                                               inductive_ind := 0
                                               |} []];
                                             tApp
                                               (tConst
                                               (MPfile
                                               ["Deriving"%bs; "Repr"%bs],
                                               "repr_arg"%bs)
                                               [Level.level "Test.222"%bs])
                                               [
                                               tApp
                                               (tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile ["Test"%bs],
                                               "mylist"%bs);
                                               inductive_ind := 1
                                               |} []) [
                                               tRel 5];
                                               tApp
                                               (tConst
                                               (MPfile ["Test"%bs],
                                               "repr_mylist2"%bs) [])
                                               [tRel 5; tRel 4]; 
                                               tRel 0];
                                             tApp
                                               (tConstruct
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "list"%bs);
                                               inductive_ind := 0
                                               |} 0 [])
                                               [
                                               tApp
                                               (tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Documents"%bs; "PPrint"%bs],
                                               "doc"%bs);
                                               inductive_ind := 0
                                               |} [])
                                               [tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "unit"%bs);
                                               inductive_ind := 0
                                               |} []]]]]]
                                |}]))));
               rarg := 3
             |};
             {|
               dname :=
                 {|
                   binder_name := nNamed "fix_mylist2"%bs;
                   binder_relevance := Relevant
                 |};
               dtype :=
                 tProd
                   {|
                     binder_name := nNamed "A0"%bs;
                     binder_relevance := Relevant
                   |}
                   (tSort
                      (sType (Universe.make' (Level.level "Test.220"%bs))))
                   (tProd
                      {|
                        binder_name := nNamed "H0"%bs;
                        binder_relevance := Relevant
                      |}
                      (tApp
                         (tInd
                            {|
                              inductive_mind :=
                                (MPfile ["Class"%bs; "Repr"%bs], "Repr"%bs);
                              inductive_ind := 0
                            |} []) [tRel 0])
                      (tProd
                         {|
                           binder_name := nNamed "min_prec"%bs;
                           binder_relevance := Relevant
                         |}
                         (tInd
                            {|
                              inductive_mind :=
                                (MPfile
                                   ["Datatypes"%bs; "Init"%bs; "Coq"%bs],
                                 "nat"%bs);
                              inductive_ind := 0
                            |} [])
                         (tProd
                            {|
                              binder_name := nNamed "x"%bs;
                              binder_relevance := Relevant
                            |}
                            (tApp
                               (tInd
                                  {|
                                    inductive_mind :=
                                      (MPfile ["Test"%bs], "mylist"%bs);
                                    inductive_ind := 1
                                  |} []) [tRel 2])
                            (tApp
                               (tInd
                                  {|
                                    inductive_mind :=
                                      (MPfile ["Documents"%bs; "PPrint"%bs],
                                       "doc"%bs);
                                    inductive_ind := 0
                                  |} [])
                               [tInd
                                  {|
                                    inductive_mind :=
                                      (MPfile
                                         ["Datatypes"%bs; "Init"%bs;
                                          "Coq"%bs], "unit"%bs);
                                    inductive_ind := 0
                                  |} []]))));
               dbody :=
                 tLambda
                   {|
                     binder_name := nNamed "A0"%bs;
                     binder_relevance := Relevant
                   |}
                   (tSort
                      (sType (Universe.make' (Level.level "Test.220"%bs))))
                   (tLambda
                      {|
                        binder_name := nNamed "H0"%bs;
                        binder_relevance := Relevant
                      |}
                      (tApp
                         (tInd
                            {|
                              inductive_mind :=
                                (MPfile ["Class"%bs; "Repr"%bs], "Repr"%bs);
                              inductive_ind := 0
                            |} []) [tRel 0])
                      (tLambda
                         {|
                           binder_name := nNamed "min_prec"%bs;
                           binder_relevance := Relevant
                         |}
                         (tInd
                            {|
                              inductive_mind :=
                                (MPfile
                                   ["Datatypes"%bs; "Init"%bs; "Coq"%bs],
                                 "nat"%bs);
                              inductive_ind := 0
                            |} [])
                         (tLambda
                            {|
                              binder_name := nNamed "x"%bs;
                              binder_relevance := Relevant
                            |}
                            (tApp
                               (tInd
                                  {|
                                    inductive_mind :=
                                      (MPfile ["Test"%bs], "mylist"%bs);
                                    inductive_ind := 1
                                  |} []) [tRel 2])
                            (tCase
                               {|
                                 ci_ind :=
                                   {|
                                     inductive_mind :=
                                       (MPfile ["Test"%bs], "mylist"%bs);
                                     inductive_ind := 1
                                   |};
                                 ci_npar := 1;
                                 ci_relevance := Relevant
                               |}
                               {|
                                 puinst := [];
                                 pparams := [tRel 3];
                                 pcontext :=
                                   [{|
                                      binder_name := nNamed "x"%bs;
                                      binder_relevance := Relevant
                                    |}];
                                 preturn :=
                                   tApp
                                     (tInd
                                        {|
                                          inductive_mind :=
                                            (MPfile
                                               [
                                               "Documents"%bs; "PPrint"%bs],
                                             "doc"%bs);
                                          inductive_ind := 0
                                        |} [])
                                     [tInd
                                        {|
                                          inductive_mind :=
                                            (MPfile
                                               [
                                               "Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "unit"%bs);
                                          inductive_ind := 0
                                        |} []]
                               |} (tRel 0)
                               [{|
                                  bcontext := [];
                                  bbody :=
                                    tApp
                                      (tConst
                                         (MPfile ["Deriving"%bs; "Repr"%bs],
                                          "repr_ctor"%bs) [])
                                      [tRel 1; tString "MyNil2";
                                       tApp
                                         (tConstruct
                                            {|
                                              inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "list"%bs);
                                              inductive_ind := 0
                                            |} 0 [])
                                         [tApp
                                            (tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Documents"%bs; "PPrint"%bs],
                                               "doc"%bs);
                                               inductive_ind := 0
                                               |} [])
                                            [tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "unit"%bs);
                                               inductive_ind := 0
                                               |} []]]]
                                |};
                                {|
                                  bcontext :=
                                    [{|
                                       binder_name := nNamed "x1"%bs;
                                       binder_relevance := Relevant
                                     |};
                                     {|
                                       binder_name := nNamed "x0"%bs;
                                       binder_relevance := Relevant
                                     |}];
                                  bbody :=
                                    tApp
                                      (tConst
                                         (MPfile ["Deriving"%bs; "Repr"%bs],
                                          "repr_ctor"%bs) [])
                                      [tRel 3; tString "MyCons2";
                                       tApp
                                         (tConstruct
                                            {|
                                              inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "list"%bs);
                                              inductive_ind := 0
                                            |} 1 [])
                                         [tApp
                                            (tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Documents"%bs; "PPrint"%bs],
                                               "doc"%bs);
                                               inductive_ind := 0
                                               |} [])
                                            [tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "unit"%bs);
                                               inductive_ind := 0
                                               |} []];
                                          tApp
                                            (tConst
                                               (
                                               MPfile
                                               ["Deriving"%bs; "Repr"%bs],
                                               "repr_arg"%bs)
                                               [
                                               Level.level "Test.223"%bs])
                                            [tRel 5; tRel 4; tRel 1];
                                          tApp
                                            (tConstruct
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "list"%bs);
                                               inductive_ind := 0
                                               |} 1 [])
                                            [tApp
                                               (tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Documents"%bs; "PPrint"%bs],
                                               "doc"%bs);
                                               inductive_ind := 0
                                               |} [])
                                               [
                                               tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "unit"%bs);
                                               inductive_ind := 0
                                               |} []];
                                             tApp
                                               (tConst
                                               (MPfile
                                               ["Deriving"%bs; "Repr"%bs],
                                               "repr_arg"%bs)
                                               [Level.level "Test.224"%bs])
                                               [
                                               tApp
                                               (tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile ["Test"%bs],
                                               "mylist"%bs);
                                               inductive_ind := 0
                                               |} []) [
                                               tRel 5];
                                               tApp
                                               (tConst
                                               (MPfile ["Test"%bs],
                                               "repr_mylist"%bs) [])
                                               [tRel 5; tRel 4]; 
                                               tRel 0];
                                             tApp
                                               (tConstruct
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "list"%bs);
                                               inductive_ind := 0
                                               |} 0 [])
                                               [
                                               tApp
                                               (tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Documents"%bs; "PPrint"%bs],
                                               "doc"%bs);
                                               inductive_ind := 0
                                               |} [])
                                               [tInd
                                               {|
                                               inductive_mind :=
                                               (MPfile
                                               ["Datatypes"%bs; "Init"%bs;
                                               "Coq"%bs], "unit"%bs);
                                               inductive_ind := 0
                                               |} []]]]]]
                                |}]))));
               rarg := 3
             |}] 0) [tRel 1; tRel 0]]))).

Time Eval vm_compute in repr big_def.
Time Eval native_compute in repr big_def.