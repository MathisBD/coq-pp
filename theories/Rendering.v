From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From PPrint Require Import Documents.

(** * Backends. *)

(** The rendering engine does not output strings directly : it is parametric over
    a backend, which provides a low-level output interface.
   
    The job of the backend is to :
    - accumulate characters and strings ([add_char], [add_string]).
    - deal with annotations ([enter_annot], [exit_annot]). 

    I chose to represent a backend as a simple state machine :
    - [initial_state] is the initial state.
    - various functions such as [add_char] or [enter_annot] modify the state.
    - [get_output] extracts the actual output (usually a string) from the state.
    This representation is simple yet seems to be general enough in practice.

    Annotations can be nested. For instance :
      [enter_annot A1 ; add_string "hello" ; enter_annot A2 ; add_string "world" ; exit_annot A2 ; exit_annot A1]
    will print "hello" with annotation [A1] followed by "world" with annotation [A2].
    Calls to [enter_annot]/[exit_annot] are always well-parenthesized.
*)
Module Type Backend.

(** The output type of this backend. 
    Usually this is [string], but it could also be some kind of HTML data-structure. *)
Parameter output : Type.

(** The type of annotations supported by this backend.
    Basic examples could be :
    - [Inductive annot := Bold | Italic | Underline.] to support bold, italic or underlined text.
    - [Record annot := { red : nat ; green : nat ; blue : nat}.] to add color to your text. 
*)
Parameter annot : Type.

(** The internal state maintainted by the backend. 
    This is implementation-specific. *)
Parameter state : Type.
  
(** The initial state. *)
Parameter init_state : state.

(** Extract the output from a state. *)
Parameter get_output : state -> output.

(** Add a single character. *)
Parameter add_char : Ascii.ascii -> state -> state.

(** Add a string. *)
Parameter add_string : String.string -> state -> state.

(** Enter an annotation : all characters and strings added between [enter_annot] and 
    the matching [exit_annot] should have the annotation [annot] applied to them. *)
Parameter enter_annot : annot -> state -> state.

(** Exit an annotation. The [annot] argument is the same as in the corresponding [enter_annot]. *)
Parameter exit_annot : annot -> state -> state.
  
End Backend.
  
(** * Rendering a document to a backend. *)

(** The rendering engine is parametric over a backend. *)
Module Make (B : Backend).

(** [make_string n c] makes a string of length [n] filled with the character [c]. *)
Definition make_string (n : nat) (c : Ascii.ascii) : String.string :=
  let fix loop n acc :=
    match n with 
    | 0 => acc
    | S n => loop n (String c acc)
    end
  in 
  loop n EmptyString.

(** [pretty doc flat width indent col st] is the main function in the rendering engine :
    - [doc] is the document we are printing.
    - [flat] is [true] if we are in flat mode, otherwise it is [false].
    - [width] is the maximum character width we are allowed to use.
    - [indent] is the current indentation level : [indent] blank characters are added after each newline.
    - [col] is the current column index, starting at 0.
    - [st] is the backend state.

    As documents can become quite big, we are careful to write this function in tail-recursive style.
    The continuation is passed : 
    - the resulting column index.
    - the resulting backend state.
*)
Fixpoint pretty {T} (doc : doc B.annot) (flat : bool) (width indent col : nat) (state : B.state) (k : nat -> B.state -> T) : T :=
  match doc with
  | Empty => k col state
  | AString len s => k (col + len) (B.add_string s state)
  | Blank n => k (col + n) (B.add_string (make_string n " "%char) state)
  | HardLine =>
      (* We should be in normal mode here. *)
      let state := B.add_char "010"%char state in
      let state := B.add_string (make_string indent " "%char) state in
      k indent state
  | IfFlat doc1 doc2 =>
      (* Print [doc1] or [doc2] depending on the current mode. *)
      pretty (if flat then doc1 else doc2) flat width indent col state k
  | Cat _ doc1 doc2 =>
      (* Print [doc1] followed by [doc2]. *)
      pretty doc1 flat width indent col state (fun col state =>
        pretty doc2 flat width indent col state k)
  | Nest _ n doc => 
      (* Simply increase the indentation amount. *)
      pretty doc flat width (indent + n) col state k
  | Group req doc =>
      (* Determine if [doc] should be flattened. *)
      let doc_flat := 
        match req with 
        | Width req => Nat.leb (col + req) width
        | Infinity => false
        end
      in
      (* Take care to stay in flattening mode if we are already in it. *)
      pretty doc (flat || doc_flat) width indent col state k
  | Align _ doc => 
      (* Set the indentation amount to the current column. *)
      pretty doc flat width col col state k
  | Annot _ ann doc =>
      let state := B.enter_annot ann state in
      pretty doc flat width indent col state (fun col state =>
        let state := B.exit_annot ann state in k col state)
  end.

(** [pp width doc] pretty-prints the document [doc] to the backend,
    using a maximum character width of [width]. *)
Definition pp `{width : nat} doc : B.output :=
  pretty doc false width 0 0 B.init_state (fun _ state => B.get_output state).

End Make.