From Coq Require Import String Ascii Decimal List.
From PPrint Require Import All.

Import ListNotations.
Open Scope string_scope.

Class Repr A : Type :=
{ 
  repr_doc : A -> doc unit
}.

Definition repr {A : Type} `{Repr A} (a : A) := @PpString.pp 80 (repr_doc a).

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

Definition string_of_nat n : string :=
  string_of_uint (Nat.to_uint n).

(** Representation of natural numbers. *)
Instance reprNat : Repr nat :=
{ 
  repr_doc n := str (string_of_nat n)
}.

(** Representation of strings. *)
Instance reprString : Repr string :=
{ 
  repr_doc s := str """" ^^ str s ^^ str """"
}.

(** Representation of pairs. *)
Instance reprPair {A B : Type} `{Repr A} `{Repr B} : Repr (A * B) :=
{
  repr_doc '(a, b) := 
    let contents := repr_doc a ^^ str "," ^^ break 1 ^^ repr_doc b in
    let res := str "(" ^^ align contents ^^ str ")" in
    group (align res)
}.

(** Representation of lists. *)
Instance reprList {A : Type} `{Repr A} : Repr (list A) :=
{
  repr_doc l := 
    let contents := flow_map (str ";" ^^ break 1) repr_doc l in
    let res := str "[" ^^ align contents ^^ str "]" in
    group (align res)
}.

Record color := { red : list nat * list nat ; green : list nat ; blue : list nat }. 

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

Fixpoint range n : list nat := 
  match n with 
  | 0 => []
  | S n => S n :: range n
  end.

Inductive level : Type :=
  | Infinity : level
  | ExtremelyLongName : nat -> list nat -> nat -> list nat -> level
  | Under : list nat * list nat -> level.

Definition repr_constr (label : string) (args : list (doc unit)) : doc unit :=
  (*let res := separate (break 1) (str label :: args) in*)
  let res := flow (break 1) (str label :: args) in
  group (hang 4 res).
  
Instance reprLevel : Repr level :=
{
  repr_doc l := 
    match l with 
    | Infinity => repr_constr "Infinity" []
    | ExtremelyLongName n ns m ms => repr_constr "ExtremelyLongName" [repr_doc n; repr_doc ns; repr_doc m ; repr_doc ms]
    | Under x => repr_constr "Under" [repr_doc x]
    end
}.

Definition l_small := ExtremelyLongName 4 [42; 41] 0 [].
Definition l_large := ExtremelyLongName 42 (range 42) 0 (range 25).

Eval compute in l_large.

Eval compute in repr l_large.

Check 
Exact 42
  [42; 41; 40; 39; 38; 37; 36; 35; 34; 33; 32; 31; 30; 29; 28; 27; 26; 25; 24;
   23; 22; 21; 20; 19; 18; 17; 16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5; 4; 3;
   2; 1] 0
  [25; 24; 23; 22; 21; 20; 19; 18; 17; 16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5;
   4; 3; 2; 1].

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

Eval compute in String "034" "Hello".

Definition pp_inductive (constructors : list (string * doc unit)) : doc unit :=
  