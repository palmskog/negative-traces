From Coq Require Import Setoid Morphisms.
Set Primitive Projections.

Record a : Type := { f : nat }.

Parameter aa : a -> a -> Prop.
Parameter nn : nat -> nat -> Prop.

Declare Instance aaeq : Equivalence aa.

Declare Instance nneq : Equivalence nn.

#[global] Instance Proper_f : Proper (aa ==> nn) f.
Admitted.

Theorem w : forall x y : a, aa x y -> nn (f x) (f y).
Proof.
  intros x y H. Fail rewrite H.
Abort.

Definition f' (x : a) : nat := f x.

#[global] Instance Proper_f' : Proper (aa ==> nn) f'.
Admitted.

Theorem w : forall x y : a, aa x y -> nn (f' x) (f' y).
Proof.
  intros x y H.
  rewrite H.
Abort.
