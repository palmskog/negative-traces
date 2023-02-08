From Coq Require Import Setoid Morphisms.
Set Primitive Projections.

Record a : Type := { f : nat }.

Parameter aa : a -> a -> Prop.
Parameter nn : nat -> nat -> Prop.

#[global] Instance Proper_f : Proper (aa ==> nn) f.
Admitted.

Theorem w : forall x y : a, aa x y -> nn (f x) (f y).
Proof.
  intros x y H. Fail rewrite H.
Abort.
