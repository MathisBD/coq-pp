From Equations Require Import Equations.

Module Vec.
Inductive t1 A : nat -> Type :=
  | VNil1 : t1 A 0 
  | VCons1 : forall n, A -> t2 A n -> t1 A (S n)
with t2 A : nat -> Type :=
| VNil2 : t2 A 0 
| VCons2 : forall n, A -> t1 A n -> t2 A (S n).

End Vec.

Module Vec'.
Inductive t1 A : nat -> Type :=
  | VNil1 : t1 A 0 
  | VCons1 : forall n, A -> t2 A n -> t1 A (S n)
with t2 A : nat -> Type :=
| VNil2 : t2 A 0 
| VCons2 : forall n, A -> t1 A n -> t2 A (S n).

End Vec'.

Print Instances Signature.
