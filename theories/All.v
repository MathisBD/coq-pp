From Coq Require Import String.
From Coq Require Import List.
Import ListNotations.

(** Export the document combinators. *)
From PPrint Require Export Documents.
(** Export the rendering engine. *)
From PPrint Require Export Rendering.

(** * Common backends. *)

(** For convenience, we instantiate the rendering engine on some common backends. *)

Module StringBackend.

(** In the state we store the list of strings printed so far, most recent first. 
    We wait until [output] to concatenate them in order to avoid the quadratic 
    cost of concatenating strings in the wrong order. *)
Definition state := list string.
Definition output := string.
Definition annot := unit.

Definition init_state : state := [].
Definition add_string s st : state := s :: st.
Definition enter_annot (_ : unit) st : state := st.
Definition exit_annot (_ : unit) st : state := st.
Definition get_output st : string := List.fold_left String.append (List.rev st) ""%string.

End StringBackend.

Module PpString := Make StringBackend.

(*Definition test : doc unit := 
  str "hello" ^//^ str "there".

Eval cbv in test.
Eval cbv in @PpString.pp 15 test.*)