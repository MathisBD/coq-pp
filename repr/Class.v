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
  @pp_string 80 (repr_doc a).
