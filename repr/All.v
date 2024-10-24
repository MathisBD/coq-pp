From Coq Require Import List Decimal String Ascii. 
From PPrint Require Import All.
From Repr Require Import Utils.

Import ListNotations.
Open Scope string_scope.

(** * Repr typeclass. *)

(** [Repr] is a typeclass for objects which can be printed to a *parseable* representation.
    That is, [repr x] should be a representation of [x] which is parseable by Coq. 
    
    This typeclass is implemented using the pretty-printing library [PPrint],
    which provides documents of type [doc unit] along with document combinators
    and a rendering engine.
*)
Class Repr A : Type :=
{ 
  (** [repr_doc x] is a low-level function which prints [x] to a document of type [doc unit].
      For a higher-level function see [repr] below. *)
  repr_doc : A -> doc unit
}.

(** [repr x] prints [x] to a string [s], such that :
    - [s] is parseable by Coq.
    - [s] parses to a value which is equal to [x] (definitionally equal, 
      although not necessarily syntactically equal). 
    
    For instance, if [l] is equal to [List.app [1; 2] [3; 4]] 
    then [repr l] could be the string "[1; 2; 3; 4]". *)
Definition repr {A : Type} `{Repr A} (a : A) := 
  (* We use a maximum character width of 80, which is standard for a text document.
     In the future we might want to make the width customizable. *)
  @PpString.pp 80 (repr_doc a).

(** * Repr instances. *)

(** Representation of booleans. *)
Instance reprBool : Repr bool :=
{
  repr_doc b := if b then str "true" else str "false"
}.

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

(*Record color := { red : list nat * list nat ; green : list nat ; blue : list nat }. 

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
ExtremelyLongName 42
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

Eval compute in String "034" "Hello".*)