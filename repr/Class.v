(** This file defines the [Repr] typeclass of printable objects. *)

From PPrint Require Import All.

(** * Repr typeclass. *)

(** [Repr] is a typeclass for objects which can be printed to a *parseable* representation.
    That is, [repr x] should be a representation of [x] which is parseable by Coq. 
    
    This typeclass is implemented using the pretty-printing library [PPrint],
    which provides documents of type [doc unit] along with document combinators
    and a rendering engine.
*)
Class Repr A : Type :=
{ 
  (** [repr_prec min_prec x] is a low-level function which prints [x] to a document of type [doc unit].
      For a higher-level function see [repr] below. 
  
      The argument [min_prec] is a _precedence level_ : it is used to determine whether 
      to enclose the result in parentheses. Higher precedences bind tighter ; 
      for instance function application has a high precedence.

      [min_prec] is the minimum precedence level required to avoid parentheses :
      one should add parentheses around [x] if and only if [x] has a precedence strictly lower than [min_prec].
      Initially [min_prec] is set to 0 ; it usually increases in recursive calls, and is sometimes reset to 0.
  *)
  repr_prec : nat -> A -> doc unit
}.

(** [repr x] prints [x] to a string [s], such that :
    - [s] is parseable by Coq.
    - [s] parses to a value which is (definitionally) equal to [x]. 
    
    For instance, if [l] is equal to [[1; 2] ++ [3; 4]] 
    then [repr l] could be the string "[1; 2; 3; 4]". *)
Definition repr {A : Type} `{Repr A} (a : A) : PrimString.string := 
  (* We use a maximum character width of 80, which is standard for a text document.
     In the future we might want to make the width customizable. *)
  pp_string 80 (repr_prec 0 a).

(** * Precedences. *)

(** [paren_if min_prec prec doc] adds parentheses around [doc] if needed.
    - [min_prec] is the minimum precedence level. 
    - [prec] is the precedence level of [doc]. *)
Definition paren_if min_prec prec d : doc unit :=
  if Nat.ltb prec min_prec then paren d else d.

(** Precedence level of a function application. *)
Definition app_precedence : nat := 1024.