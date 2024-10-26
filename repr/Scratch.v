From Coq Require Import List.
From MetaCoq.Template Require Import All.
Import MCMonadNotation ListNotations.


Print term.

Check 42.
Check 43.
About Nat.add.

(** Comment above x. *)
Definition x := 3.

Print term.

Print Nat.add.

Fixpoint f n :=
  match n with 
  | S n => 
    mlet t_n <- tmQuote 0 ;;
    mlet fn <- f n ;;
    ret (t_n :: fn)
  | 0 => 
    mlet t_0 <- tmQuote 0 ;;
    ret [t_0]
  end.

Time MetaCoq Run (f 100).
Time MetaCoq Run (f 200).
Time MetaCoq Run (f 300).
Time MetaCoq Run (f 400).
Time MetaCoq Run (f 500).
Time MetaCoq Run (f 600).
Time MetaCoq Run (f 700).
Time MetaCoq Run (f 800).
Time MetaCoq Run (f 900).
Time MetaCoq Run (f 1000).

(*
N   | Time (seconds)
----|---------------
100 | 0.3
200 | 1.2
300 | 2.8
400 | 5.0
500 | 7.7
600 | 11.6
700 | 15.9
800 | 20.2
900 | 26.8
1000| 32.8
*)

Fixpoint g n : nat :=
  match n with 
  | S n => let gn := g n in S n * gn
  | 0 => 0
  end.

Time Eval compute in g 600.