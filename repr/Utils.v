From Coq Require Import Decimal String Ascii.
Open Scope string_scope.

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
