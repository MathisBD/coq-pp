From Coq Require Import Decimal String Ascii List.
From MetaCoq.Utils Require Import monad_utils.

Import ListNotations MCMonadNotation.
Open Scope string_scope.

Set Universe Polymorphism.

(** [string_of_uint n] prints the uint [n] to a string in base 10. *)
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

(** [string_of_nat n] prints the natural number [n] to a string in base 10. *)
Definition string_of_nat n : string :=
  string_of_uint (Nat.to_uint n).

(** [monad_mapi f l] is the same as [monad_map f l] except the function [f]
    is fed the index of each argument. *)
Definition monad_mapi (T : Type -> Type) (M : Monad T) (A B : Type) (f : nat -> A -> T B) (l : list A) :=
  let fix loop i l :=
    match l with
    | [] => ret []
    | x :: l => 
      mlet x' <- f i x ;;
      mlet l' <- loop (S i) l ;;
      ret (x' :: l')
    end
  in loop 0 l.

Arguments monad_mapi {T}%_function_scope {M} {A B}%_type_scope f%_function_scope l%_list_scope.
