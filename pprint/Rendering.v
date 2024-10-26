From Coq Require Import String Ascii List.
From PPrint Require Import Monad Documents.
Import ListNotations.
Open Scope monad_scope.

Set Universe Polymorphism.

(** * Pretty-printing monads. *)

(** The rendering engine does not output strings directly : it is parametric over
    a pretty-printing monad, which provides a low-level output interface.
   
    The job of the pretty-printing monad is to :
    - accumulate characters and strings ([add_string]).
    - deal with annotations ([enter_annot], [exit_annot]). 

    Annotations can be nested. For instance :
      [enter_annot A1 ;; add_string "hello" ;; enter_annot A2 ;; add_string "world" ;; exit_annot A2 ;; exit_annot A1]
    will print "hello" with annotation [A1] followed by "world" with annotation [A2].
    Calls to [enter_annot]/[exit_annot] are always well-parenthesized.
*)
Class MonadPPrint (M : Type -> Type) :=
{
  (*** The type of annotations supported by this monad. *)
  annot : Type ;

  add_string : string -> M unit ;
  enter_annot : annot -> M unit ;
  exit_annot : annot -> M unit ;
}.

(** * Rendering a document. *)

(** [make_string n c] makes a string of length [n] filled with the character [c]. *)
Definition make_string (n : nat) (c : Ascii.ascii) : string :=
  let fix loop n acc :=
    match n with 
    | 0 => acc
    | S n => loop n (String c acc)
    end
  in 
  loop n EmptyString.

Section Rendering.
(** The rendering engine is parameterized by a pretty printing monad. *)
Context {M : Type -> Type} {MonadM : Monad M} {MonadPPrintM : MonadPPrint M}.

(** [prettyM doc flat width indent col] is the main function in the rendering engine :
    - [doc] is the document we are printing.
    - [flat] is [true] if we are in flat mode, otherwise it is [false].
    - [width] is the maximum character width we are allowed to use.
    - [indent] is the current indentation level : [indent] blank characters are added after each newline.
    - [col] is the current column index, starting at 0.
    The return value contains the updated column index.

    Making this function tail recursive would require a bit more work.
    I would have to define a [MonadTailRec] class (as in PureScript for instance),
    and require a [MonadTailRec] instance on the pretty printing monad [M].
*)
Fixpoint prettyM (doc : doc annot) (flat : bool) (width indent col : nat) : M nat :=
  match doc with
  | Empty => ret col
  | Str len s => add_string s ;; ret (col + len)
  | Blank n => add_string (make_string n " "%char) ;; ret (col + n)
  | HardLine => 
    (* We should be in normal mode here. *)
    add_string (make_string 1 "010"%char) ;; 
    add_string (make_string indent " "%char) ;;
    ret indent
  | IfFlat doc1 doc2 =>
      (* Print [doc1] or [doc2] depending on the current mode. *)
      prettyM (if flat then doc1 else doc2) flat width indent col
  | Cat _ doc1 doc2 =>
      (* Print [doc1] followed by [doc2], threading the column index. *)
      bind (prettyM doc1 flat width indent col) (fun col =>
        prettyM doc2 flat width indent col)
  | Nest _ n doc => 
      (* Simply increase the indentation amount. *)
      prettyM doc flat width (indent + n) col
  | Group req doc =>
      (* Determine if [doc] should be flattened. *)
      let doc_flat := 
        match req with 
        | Width req => Nat.leb (col + req) width
        | Infinity => false
        end
      in
      (* Take care to stay in flattening mode if we are already in it. *)
      prettyM doc (flat || doc_flat) width indent col
  | Align _ doc => 
      (* Set the indentation amount to the current column. *)
      prettyM doc flat width col col
  | Annot _ ann doc =>
      enter_annot ann ;;
      mlet col <- prettyM doc flat width indent col ;;
      exit_annot ann ;;
      ret col
  end.

(** [pp width doc] pretty-prints the document [doc],
    using a maximum character width of [width]. *)
Definition ppM {width : nat} doc : M unit :=
  prettyM doc false width 0 0 ;; ret tt.

End Rendering.

(** * Basic MonadPPrint instance. *)

Definition PPString A := list string -> A * list string.

Instance monad_ppstring : Monad PPString :=
{
  ret _ x ls := (x, ls) ;
  bind _ _ mx mf ls :=
    let (x, ls) := mx ls in
    mf x ls
}.

Instance monad_pprint_ppstring : MonadPPrint PPString :=
{
  annot := unit ;
  add_string s ls := (tt, s :: ls) ;
  enter_annot _ := ret tt ;
  exit_annot _ := ret tt
}.

Definition pp_string {width : nat} doc : string :=
  let '(_, output) := @ppM PPString _ monad_pprint_ppstring width doc [] in
  List.fold_left String.append (List.rev output) EmptyString.