From Coq Require Import Strings.String.

(** This module implements a pretty-printing combinator library. 
    It is based on François Pottier's Pprint library : https://github.com/fpottier/pprint.

    It has the particularity of printing documents that can contain *annotated* text : 
    we can box pieces of text in an annotation of any type. 
    Examples of annotations include :
    - colors
    - typographical emphasis (bold, italic, underline, etc)
    It is up to the user to choose which annotations to use.

    Annotations have no effect on text layout : to print to plain text
    we can simply ignore all annotations.

    Author : Mathis Bouverot-Dupuis. 
*)



(* TODO : explain the two modes (flattening and normal). *)


(** * Width requirements. *)

(** All documents have a space requirement. This is the document's apparent length, 
    if printed in *flattening* mode. 
    This information is computed in a bottom-up manner when the document is constructed.

    In other words, the space requirement is the number of columns that the
    document needs in order to fit on a single line.
*)
Inductive requirement :=
  | (** [Infinity] is used for a document which cannot be printed on single line.
        This happens e.g. if the document contains a hardline. *)
    Infinity : requirement 
  | (** [Width n] is used for a document which takes [n] characters in flat mode. *)
    Width : nat -> requirement. 

(** [add_requirements r1 r2] adds the requirements [r1] and [r2], 
    taking care that adding infinity results in infinity. *)
Definition add_requirements (r1 r2 : requirement) : requirement :=
  match r1, r2 with 
  | Width w1, Width w2 => Width (w1 + w2)
  | _, _ => Infinity
  end. 

(** * Documents. *)

(** The type of documents, which depends on the type of annotations.
    The only construct which actually uses annotations is [Annot]. *)
Inductive doc (A : Type) : Type :=   
  (* [Empty] is the empty document. *)
  | Empty : doc A
  (* [Blank n] is an atomic document that consists of [n] blank characters. *)
  | Blank : nat -> doc A
  (* [AString len s] is an atomic string [s] of length [len]. 
     We assume (but do not check) that strings do not contain a newline character. *)
  | AString : nat -> string -> doc A
  (* [IfFlat d1 d2] turns into the document :
     - [d1] in flattening mode.
     - [d2] in normal mode. 
     
     We maintain the invariant that [d1] should not itself be of the form [IfFlat _ _].
     Users should use the function [ifflat] defined below to ensure this invariant is preserved.
  *)
  | IfFlat : doc A -> doc A -> doc A
  (* When in flattening mode, [HardLine] causes a failure, which requires
     backtracking all the way until the stack is empty. When not in flattening
     mode, it represents a newline character, followed with an appropriate
     number of indentation. A common way of using [HardLine] is to only use it
     directly within the right branch of an [IfFlat] construct. *)
  | HardLine
  (* [Cat req doc1 doc2] is the concatenation of the documents [doc1] and [doc2]. 
     The space requirement [req] is the sum of the requirements of [doc1] and [doc2]. *)
  | Cat : requirement -> doc A -> doc A -> doc A
  (* [Nest req n doc] is the document [doc], in which the indentation
     level has been increased by [n], that is in which [n] blanks have been
     inserted after every newline character. 
     The space requirement [req] is the same as the requirement of [doc]. *)
  | Nest : requirement -> nat -> doc A -> doc A
  (* [Group req doc] represents an alternative: it is either a flattened
     form of [doc], in which occurrences of [Group] disappear and occurrences
     of [IfFlat] resolve to their left branch, or [doc] itself. 
     The space requirement [req] is the same as the requirement of [doc]. *)
  | Group : requirement -> doc A -> doc A
  (* [Align req doc] increases the indentation level to reach the current column.
     Thus, the document [doc] is rendered within a box whose upper
     left corner is the current position.
     The space requirement [req] is the same as the requirement of [doc]. *)
  | Align : requirement -> doc A -> doc A
    (* [Annot req ann doc] annotates the document [doc] with annotation [ann].
       The space requirement [req] is the same as the requirement of [doc]. *)
  | Annot : requirement -> A -> doc A -> doc A.

Arguments Empty    {A}%_type_scope.
Arguments Blank    {A}%_type_scope.
Arguments AString   {A}%_type_scope.
Arguments IfFlat   {A}%_type_scope.
Arguments HardLine {A}%_type_scope.
Arguments Cat      {A}%_type_scope.
Arguments Nest     {A}%_type_scope.
Arguments Group    {A}%_type_scope.
Arguments Align    {A}%_type_scope.
Arguments Annot    {A}%_type_scope.

(** Retrieve or compute the space requirement of a doc. This is constant-time. *)
Fixpoint doc_requirement {A} (d : doc A) : requirement :=
  match d with 
  | Empty => Width 0
  | Blank len => Width len
  | AString len _ => Width len
  | IfFlat doc1 _ => doc_requirement doc1
  | HardLine => Infinity
  | Cat req _ _ => req
  | Nest req _ _ => req
  | Group req _ => req
  | Align req _ => req
  | Annot req _ _ => req
  end.

(** Storing requirement information at [Group] nodes is crucial, as it allows us to
    avoid backtracking and buffering.

    Storing this information at other nodes allows the function [doc_requirement]
    to operate in constant time. This means that the bottom-up computation of
    requirements takes linear time. 
*)

(** * Basic combinators. *)
    
Section BasicCombinators.
Context {A : Type}.

(** [empty] is the empty document. *)
Definition empty : doc A := Empty.

(** [char c] is an atomic document that consists of the single character [c].
    This character must not be a newline character, although we do not check it. *)
Definition char c : doc A := 
  AString 1 (String c EmptyString).

(** [string s] is an atomic document that consists of the string [s]. 
    This string must not contain a newline. *)
Definition string s : doc A :=
  AString (String.length s) s.

(** The atomic document [hardline] represents a forced newline. 
    This document has infinite ideal width: thus, if there is a choice between printing it
    in flat mode and printing it in normal mode, normal mode is preferred. 
    In other words, when [hardline] is placed directly inside a group, this
    group is dissolved: [group hardline] is equivalent to [hardline]. 
    This combinator should be seldom used; consider using [break] instead. *)
Definition hardline : doc A := HardLine.
    
(** The atomic document [blank n] consists of [n] blank characters. 
    A blank character is like an ordinary ASCII space character [char ' '], 
    except that blank characters that appear at the end of a line are automatically suppressed. *)
Definition blank n : doc A := Blank n.
    
(** [space] is a synonym for [blank 1]. It consists of one blank character.
    It is therefore not equivalent to [char ' ']. *)
Definition space : doc A := Blank 1.
   

(** [iffflat doc1 doc2] produces a document which is printed as :
    - [doc1] in flat mode. 
    - [doc2] in normal mode. *)
Definition ifflat doc1 doc2 : doc A :=
  match doc1 with 
  | IfFlat doc1 _ => IfFlat doc1 doc2
  | _ => IfFlat doc1 doc2
  end.

(** The document [break n] is a breakable blank of width [n]. It is printed as :
    - [n] blank characters in flat mode, 
    - a single newline character in normal mode. *)
Definition break (n : nat) : doc A := ifflat (blank n) hardline.
  
(** [doc1 ^^ doc2] is the concatenation of the documents [doc1] and [doc2]. *) 
Definition cat doc1 doc2 : doc A :=
  match doc1, doc2 with 
  | Empty, _ => doc2
  | _, Empty => doc1
  | _, _ => Cat (add_requirements (doc_requirement doc1) (doc_requirement doc2)) doc1 doc2
  end.
Notation "d1 ^^ d2" := (cat d1 d2) (at level 60, right associativity).


(** [group doc] encodes a choice. If the document [doc] fits on the current
    line, then it is rendered on a single line, in flat mode. (All [group]
    combinators inside it are then ignored.) Otherwise, this group is
    dissolved and [doc] is rendered in normal mode. There might be more
    groups within [doc], whose presence leads to further choices being
    explored. *)
Definition group d : doc A :=
  match doc_requirement d with
  | Infinity => d
  | req => Group req d
  end.
   
(** To render the document [nest n doc], the printing engine temporarily
    increases the current indentation level by [n], then renders [doc]. 
    The effect of the current indentation level is as follows: every time a
    newline character is emitted, it is immediately followed by [n] blank
    characters, where [n] is the current indentation level. 
    Thus, one may think of [nest n doc] roughly as the document [doc] in which [n] blank
    characters have been inserted after every newline character. *)
Definition nest n d : doc A :=
  Nest (doc_requirement d) n d.

(** To render [align doc], the printing engine sets the current indentation
    level to the current column, then renders [doc]. In other words, the
    document [doc] is rendered within a box whose upper left corner is the
    current position of the printing engine. *)
Definition align d : doc A :=
  Align (doc_requirement d) d.

(** [annotate ann doc] is rendered as [doc], surrounded by the annotation [ann].
    The meaning of annotations is backend-dependent (see below). *)
Definition annotate annot d : doc A := 
  Annot (doc_requirement d) annot d.
  
End BasicCombinators.

(** * High-level combinators. *)

  (*  (** [repeat n doc] is the document obtained by concatenating [n] copies of
        the document [doc]. *)
    val repeat : int -> 'a doc -> 'a doc
    
    (** [concat docs] is the concatenation of the documents in the list [docs]. *)
    val concat : 'a doc list -> 'a doc
    
    (** [separate sep docs] is the concatenation of the documents in the list
        [docs]. The separator [sep] is inserted between every two adjacent documents. *)
    val separate : 'a doc -> 'a doc list -> 'a doc
    
    (** [optional f None] is the empty document. [optional f (Some x)] is
        the document [f x]. *)
    val optional : ('a -> 'a doc) -> 'a option -> 'a doc
    
    (** [hang n doc] is analogous to [align], but additionally indents all lines,
        except the first one, by [n]. Thus, the text in the box forms a hanging
        indent. *)
    val hang : int -> 'a doc -> 'a doc
    
    (** [prefix n b left right] has the following flat layout:
        {[
          left right
        ]}
        and the following non-flat layout:
        {[
          left
            right
        ]}
        The parameter [n] controls the nesting of [right] (when not flat).
        The parameter [b] controls the number of spaces between [left] and [right]
        (when flat). *)
    val prefix : int -> int -> 'a doc -> 'a doc -> 'a doc
    
    (**[infix n b middle left right] has the following flat layout:
       {[
         left middle right
       ]}
       and the following non-flat layout:
       {[
         left middle
           right
       ]}
       The parameter [n] controls the nesting of [right] (when not flat).
       The parameter [b] controls the number of spaces between [left] and [middle]
       (always) and between [middle] and [right] (when flat). *)
    val infix : int -> int -> 'a doc -> 'a doc -> 'a doc -> 'a doc
    
    (** [flow sep docs] separates the documents in the list [docs] with the
        separator [sep] and arranges for a new line to begin whenever a document
        does not fit on the current line. This is useful for typesetting
        free-flowing, ragged-right text. A typical choice of [sep] is [break b],
        where [b] is the number of spaces that must be inserted between two
        consecutive words (when displayed on the same line). *)
    val flow : 'a doc -> 'a doc list -> 'a doc
    
    (** [flow_map sep f docs] is equivalent to [flow sep (List.map f docs)]. *)
    val flow_map : 'a doc -> ('b -> 'a doc) -> 'b list -> 'a doc
    
    (** [x ^+^ y] separates [x] and [y] with a non-breakable space.
        It is a short-hand for [x ^^ space ^^ y]. *)
    val ( ^+^ ) : 'a doc -> 'a doc -> 'a doc
    
    (** [x ^/^ y] is a short-hand for [prefix 0 1 x y]. 
        
        It has the following flat layout : 
        {[
          x y
        ]} 
        and the following non-flat layout : 
        {[
          x 
          y
        ]} *)
    val ( ^/^ ) : 'a doc -> 'a doc -> 'a doc
    
    (** [x ^//^ y] is a short-hand for [prefix 2 1 x y]. 
        
        It has the following flat layout : 
        {[
          x y
        ]} 
        and the following non-flat layout : 
        {[
          x 
            y
        ]} *)
    val ( ^//^ ) : 'a doc -> 'a doc -> 'a doc*)
    
