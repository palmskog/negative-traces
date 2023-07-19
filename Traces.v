From Coq Require Import RelationClasses Program.Basics.
From Coinduction Require Import all.

Import CoindNotations.

Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

Section Trace.

Context {A B : Type}.

Variant traceF (trace : Type) : Type :=
| TnilF (a : A)
| TconsF (a : A) (b : B) (tr : trace).

CoInductive trace : Type := go { _observe : traceF trace }.

End Trace.

Declare Scope trace_scope.
Bind Scope trace_scope with trace.
Delimit Scope trace_scope with trace.
Local Open Scope trace_scope.

Arguments trace _ _ : clear implicits.
Arguments traceF _ _ : clear implicits.

Notation trace' A B := (traceF A B (trace A B)).

Definition observe {A B} (tr : trace A B) : trace' A B :=
@_observe A B tr.

Notation Tnil a := (go (TnilF a)).
Notation Tcons a b tr := (go (TconsF a b tr)).

Section Operations.

Context {A B : Type}.

Definition hd (tr : trace A B) : A :=
match observe tr with
| TnilF a => a
| TconsF a b tr0 => a
end.

Definition tr_app : trace A B -> trace A B -> trace A B :=
 cofix _tr_app (tr tr' : trace A B) :=
  match observe tr with
  | TnilF a => tr'
  | TconsF a b tr0 => Tcons a b (_tr_app tr0 tr')
  end.

End Operations.

Module TraceNotations.
Infix "+++" := tr_app (at level 60, right associativity) : trace_scope.
End TraceNotations.

Section Eqtr.

Context {A B : Type}.

Variant eqtrb (eq : trace A B -> trace A B -> Prop) :
 trace' A B -> trace' A B -> Prop :=
| Eq_Tnil a : eqtrb eq (TnilF a) (TnilF a)
| Eq_Tcons a b tr1 tr2 (REL : eq tr1 tr2) :
   eqtrb eq (TconsF a b tr1) (TconsF a b tr2).
Hint Constructors eqtrb: core.

Definition eqtrb_ eq : trace A B -> trace A B -> Prop :=
 fun tr1 tr2 => eqtrb eq (observe tr1) (observe tr2).

Program Definition feqtr: mon (trace A B -> trace A B -> Prop) := {| body := eqtrb_ |}.
Next Obligation.
  unfold pointwise_relation, Basics.impl, eqtrb_.
  intros ?? INC ?? EQ. inversion_clear EQ; auto.
Qed.

End Eqtr.

Definition eqtr {A B} := (gfp (@feqtr A B)).
#[global] Hint Unfold eqtr: core.
#[global] Hint Constructors eqtrb: core.
Arguments eqtrb_ _ _/.

Ltac fold_eqtr :=
  repeat
    match goal with
    | h: context[@feqtr ?A ?B] |- _ => fold (@eqtr A B) in h
    | |- context[@feqtr ?A ?B] => fold (@eqtr A B)
    end.

#[export] Instance Reflexive_eqtrb {A B : Type} {R} {Hr: Reflexive R} :
 Reflexive (@eqtrb A B R).
Proof. now intros [a|a b tr]; constructor. Qed.

#[export] Instance Reflexive_feqtr {A B : Type} : forall {R: Chain (@feqtr A B)}, Reflexive `R.
Proof. apply Reflexive_chain. now cbn. Qed.

#[export] Instance Symmetric_eqtrb {A B : Type} {R} {Hr: Symmetric R} :
 Symmetric (@eqtrb A B R).
Proof.
intros [a|a b tr].
- intros [a'|a' b' tr'] Heq.
  * inversion Heq; subst.
    constructor.
  * inversion Heq.
- intros [a'|a' b' tr'] Heq.
  * inversion Heq.
  * inversion Heq; subst.
    constructor.
    symmetry.
    assumption.
Qed.

#[export] Instance Symmetric_feqtr {A B : Type} : forall {R: Chain (@feqtr A B)}, Symmetric `R.
Proof.
  apply Symmetric_chain. 
  intros R HR.
  intros x y xy.
  now apply Symmetric_eqtrb.
Qed.

#[export] Instance Transitive_eqtrb {A B : Type} {R} {Hr: Transitive R} :
 Transitive (@eqtrb A B R).
Proof.
intros [xa|xa xb xtr]; intros [ya|ya yb ytr]; intros [za|za zb ztr] Heqx Heqy.
- inversion Heqx; subst.
  inversion Heqy; subst.
  constructor.
- inversion Heqy; subst.
- inversion Heqx.
- inversion Heqx.
- inversion Heqx.
- inversion Heqx.
- inversion Heqy.
- inversion Heqx; subst.
  inversion Heqy; subst.
  constructor.
  revert REL REL0.
  apply Hr.
Qed.

#[export] Instance Transitive_feqtr {A B : Type} : forall {R: Chain (@feqtr A B)}, Transitive `R.
Proof.
  apply Transitive_chain. 
  intros R HR.
  intros x y z.
  now apply Transitive_eqtrb.
Qed.

#[export] Instance Equivalence_eqtr {A B}: Equivalence (@eqtr A B).
Proof. split; typeclasses eauto. Qed.

Lemma eqtr_eta_ {A B : Type} (tr : trace A B) : eqtr tr (go (_observe tr)).
Proof. now step. Qed.

Lemma eqtr_eta {A B : Type} (tr : trace A B) : eqtr tr (go (observe tr)).
Proof. now step. Qed.

CoFixpoint zeros : trace nat unit := Tcons 0 tt zeros.
Definition zeros' : trace nat unit := Tcons 0 tt (Tcons 0 tt zeros).

Lemma zeros_zeros_eqtr : eqtr zeros zeros.
Proof. reflexivity. Qed.

Lemma zeros_zeros_one_eqtr : eqtr zeros (Tcons 0 tt zeros).
Proof. unfold eqtr; step; cbn; reflexivity. Qed.

Lemma zeros_zeros'_eqtr : eqtr zeros zeros'.
Proof.
unfold eqtr, zeros'.
step; cbn; constructor; cbn.
apply zeros_zeros_one_eqtr.
Qed.

#[export] Instance Proper_eqtr {A B} :
  Proper (eqtr ==> eqtr ==> flip impl) (@eqtr A B).
Proof.
unfold Proper, respectful, flip, impl; cbn.
unfold eqtr; intros.
transitivity y; auto.
symmetry in H0.
transitivity y0; auto.
Qed.

Lemma eqtr_Tnil_inv {A B : Type} (a1 a2 : A) :
 @eqtr A B (Tnil a1) (Tnil a2) ->
 a1 = a2.
Proof.
unfold eqtr; intros Heq.
apply (gfp_fp feqtr) in Heq.
cbn in Heq.
inversion Heq; subst.
reflexivity.
Qed.

Lemma eqtr_Tcons_inv {A B : Type} a1 a2 b1 b2 (tr1 tr2 : trace A B) :
 eqtr (Tcons a1 b1 tr1) (Tcons a2 b2 tr2) ->
 a1 = a2 /\ b1 = b2 /\ eqtr tr1 tr2.
Proof.
unfold eqtr; intros Heq.
apply (gfp_fp feqtr) in Heq.
cbn in Heq.
inversion Heq; subst.
tauto.
Qed.

Lemma eqtr_hd {A B : Type} (tr1 tr2 : trace A B) :
 eqtr tr1 tr2 -> hd tr1 = hd tr2.
Proof.
unfold eqtr, hd; intros Heq.
apply (gfp_fp feqtr) in Heq.
cbn in Heq.
destruct (observe tr1) eqn:?;
 destruct (observe tr2) eqn:?.
- inversion Heq; subst; reflexivity.
- inversion Heq.
- inversion Heq.
- inversion Heq; subst; reflexivity.
Qed.

Import TraceNotations.

Lemma observe_Tnil_tr_app {A B} : forall a (tr : trace A B),
 observe (Tnil a +++ tr) = observe tr.
Proof.
intros a tr; reflexivity.
Qed.

Lemma observe_Tnil_tr_app' {A B} : forall (a : A) (tr tr' : trace A B),
 observe tr = @TnilF A B _ a ->
 observe (tr +++ tr') = observe tr'.
Proof.
intros a tr tr' Heq; unfold tr_app.
destruct (observe tr) eqn:?.
- cbv in *.
  inversion Heq; subst.  
  rewrite Heqt.
  reflexivity.
- inversion Heq.
Qed.

Lemma eqtr_Tnil_tr_app {A B} : forall a (tr : trace A B), eqtr (Tnil a +++ tr) tr.
Proof.
intros a tr; unfold eqtr.
step; reflexivity.
Qed.

Lemma observe_Tcons_tr_app {A B} : forall a b (tr tr' : trace A B),
 observe (Tcons a b tr +++ tr') = observe (Tcons a b (tr +++ tr')).
Proof.
intros a b tr tr'.
reflexivity.
Qed.

Lemma eqtr_Tcons_tr_app {A B} : forall a b (tr tr' : trace A B),
 eqtr (Tcons a b tr +++ tr') (Tcons a b (tr +++ tr')).
Proof.
intros a b tr tr'.
step.
reflexivity.
Qed.

Lemma observe_Tcons_tr_app' {A B} : forall (a : A) (b : B) (tr tr0 tr' : trace A B),
 observe tr = @TconsF A B _ a b tr0 ->
 observe (tr +++ tr') = observe (Tcons a b (tr0 +++ tr')).
Proof.
intros a b tr tr0 tr' Heq; unfold tr_app.
destruct (observe tr) eqn:?.
- inversion Heq.
- cbv in *.
  inversion Heq; subst.
  rewrite Heqt.
  reflexivity.
Qed.

Lemma observe_Tcons_tr_app'' {A B} : forall a b tr0 (tr tr' : trace A B),
 observe tr = @TconsF A B _ a b tr0 ->
 eqtr (tr +++ tr') (Tcons a b tr0 +++ tr').
Proof.
intros a b tr0 tr tr' Htr.
step.
rewrite (observe_Tcons_tr_app' _ _ Htr).
cbn.
constructor.
reflexivity.
Qed.

Lemma eqtr_tr_app_left {A B} :
forall (tr11 tr12 tr : trace A B),
 eqtr tr11 tr12 ->
 eqtr (tr11 +++ tr) (tr12 +++ tr).
Proof.
unfold eqtr; intros tr11 tr12 tr Heq.
coinduction R H.
destruct (observe tr11) eqn:?.
- cbn.
  apply (gfp_fp feqtr) in Heq.
  cbn in Heq.
  rewrite Heqt in Heq.
  inversion Heq; subst.
  rewrite (observe_Tnil_tr_app' _ _ Heqt).
  symmetry in H2.
  rewrite (observe_Tnil_tr_app' _ _ H2).
  reflexivity.
- cbn.
  apply (gfp_fp feqtr) in Heq.
  cbn in Heq.
  rewrite Heqt in Heq.
  inversion Heq; subst.
  rewrite (observe_Tcons_tr_app' _ _ Heqt).
  symmetry in H4.
  rewrite (observe_Tcons_tr_app' _ _ H4).
  cbn.
  constructor.
Abort.

(*
Lemma eqtr_tr_app {A B} : forall (tr1 tr2 tr3 tr4 : trace A B), 
 eqtr tr1 tr2 -> eqtr tr3 tr4 -> eqtr (tr1 +++ tr3) (tr2 +++ tr4).
Proof.
unfold eqtr.
intros tr1 tr2 tr3 tr4 Htr Htr'.
destruct (observe tr1) eqn:?.
- apply (gfp_fp feqtr) in Htr.
  apply (gfp_fp feqtr) in Htr'.
  cbn in Htr.
  cbn in Htr'.
  rewrite Heqt in Htr.
  inversion Htr; subst.
  symmetry in H.
  step.
  rewrite (observe_Tnil_tr_app' _ _ Heqt).
  rewrite (observe_Tnil_tr_app' _ _ H).  
  assumption.
- apply (gfp_fp feqtr) in Htr.
  apply (gfp_fp feqtr) in Htr'.
  cbn in Htr.
  cbn in Htr'.
  rewrite Heqt in Htr.
  inversion Htr; subst.
  symmetry in H.
  pose proof (observe_Tcons_tr_app'' _ tr3 Heqt).
  pose proof (observe_Tcons_tr_app'' _ tr4 H).
  cut (gfp feqtr (Tcons a b tr +++ tr3) ((Tcons a b tr5 +++ tr4))). {
    intros Heq.
    transitivity (Tcons a b tr +++ tr3); [assumption|].
    transitivity (Tcons a b tr5 +++ tr4); [assumption|].
    symmetry.
    assumption.
  }
  clear Htr Htr' Heqt H H0 H1.
  revert H0.
  coinduction R H2.
  step.
  rewrite observe_Tcons_tr_app.
  rewrite observe_Tcons_tr_app.
  cbn.
  constructor.
  transitivity (Tcons a b tr +++ tr3).
  

  apply (gfp_fp feqtr) in H0.
  apply (gfp_fp feqtr) in H1.
  coinduction R H2.
  cbn.
  rewrite (observe_Tcons_tr_app' _ _ Heqt).
  rewrite (observe_Tcons_tr_app' _ _ H).  
  cbn.
  constructor.
  apply H0.
  
  coinduction R H.

  constructor.
  step.

  cbn in H.
  cbn in H0.
  rewrite Heqt in H.
  inversion H; subst.
  symmetry in H3.
  cbv in *.
  rewrite Heqt, H3.
  assumption.
- intros; step.
  apply (gfp_fp feqtr) in H.
  apply (gfp_fp feqtr) in H0.
  cbn in H.
  cbn in H0.
  rewrite Heqt in H.
  inversion H; subst.
  symmetry in H5.
  cbv in *.
  rewrite Heqt, H5.
  constructor.
Admitted.
*)
