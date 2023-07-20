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

Definition tr_hd (tr : trace A B) : A :=
match observe tr with
| TnilF a => a
| TconsF a b tr0 => a
end.

Definition tr_app' (tr' : trace A B) : trace' A B -> trace A B :=
 cofix _tr_app (tr : trace' A B) :=
 match tr with
  | TnilF a => tr'
  | TconsF a b tr0 => Tcons a b (_tr_app (observe tr0) )
  end.

Definition tr_app : trace A B -> trace A B -> trace A B :=
 fun tr tr' => tr_app' tr' (observe tr).

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
#[export] Hint Unfold eqtr: core.
#[export] Hint Constructors eqtrb: core.
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
intros [a|a b tr]; intros [a'|a' b' tr'] Heq.
- inversion Heq; subst.
  constructor.
- inversion Heq.
- inversion Heq.
- inversion Heq; subst.
  constructor; now symmetry.
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
  inversion Heqy; subst; constructor.
- inversion Heqy; subst.
- inversion Heqx.
- inversion Heqx.
- inversion Heqx.
- inversion Heqx.
- inversion Heqy.
- inversion Heqx; subst.
  inversion Heqy; subst.
  constructor; revert REL REL0; apply Hr.
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
 eqtr tr1 tr2 -> tr_hd tr1 = tr_hd tr2.
Proof.
unfold eqtr, tr_hd; intros Heq.
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

Lemma tr_app_unfold {A B} :
  forall (tr tr' : trace A B),
    eqtr (tr +++ tr')
      (match observe tr with
       | TnilF a => tr'
       | TconsF a b tr0 => Tcons a b (tr0 +++ tr')
       end).
Proof.
  intros; now step.
Qed.

Lemma eqtr_Tnil_tr_app {A B} : forall a (tr : trace A B), eqtr (Tnil a +++ tr) tr.
Proof.
intros a tr; unfold eqtr.
step; reflexivity.
Qed.

Lemma eqtr_left_Tnil_tr_app {A B} :
forall a (tr1 tr2 : trace A B),
 eqtr (Tnil a +++ tr1) (Tnil a +++ tr2) ->
 eqtr tr1 tr2.
Proof.
intros a tr1 tr2.
rewrite tr_app_unfold.
rewrite tr_app_unfold.
cbn; auto.
Qed.

Lemma eqtr_left_tr_app_Tnil {A B} :
forall a (tr1 tr2 : trace A B),
 eqtr tr1 tr2 ->
 eqtr (Tnil a +++ tr1) (Tnil a +++ tr2).
Proof.
intros a tr1 tr2.
rewrite tr_app_unfold.
rewrite tr_app_unfold.
cbn; auto.
Qed.

Lemma eqtr_Tcons_tr_app {A B} : forall a b (tr tr' : trace A B),
 eqtr (Tcons a b tr +++ tr') (Tcons a b (tr +++ tr')).
Proof.
intros a b tr tr'.
step.
reflexivity.
Qed.

Lemma eqtr_tr_app_left {A B} :
forall (tr11 tr12 tr : trace A B),
 eqtr tr11 tr12 ->
 eqtr (tr11 +++ tr) (tr12 +++ tr).
Proof.
unfold eqtr at 2.
coinduction r h; intros tr11 tr12 tr Heq.
apply (gfp_fp feqtr) in Heq.
rewrite tr_app_unfold.
symmetry.
rewrite tr_app_unfold.
symmetry.
inversion Heq; auto.
constructor.
apply h, REL.
Qed.

Lemma eqtr_tr_app {A B} : forall (tr1 tr2 tr3 tr4 : trace A B), 
 eqtr tr1 tr2 ->
 eqtr tr3 tr4 ->
 eqtr (tr1 +++ tr3) (tr2 +++ tr4).
Proof.
unfold eqtr at 3.
coinduction R H; intros tr1 tr2 tr3 tr4 Htr Htr'.
apply (gfp_fp feqtr) in Htr.
rewrite tr_app_unfold.
symmetry.
rewrite tr_app_unfold.
symmetry.
inversion Htr; auto.
- rewrite Htr'; reflexivity.
- constructor.
  apply H; [assumption|].
  apply (gfp_fp feqtr) in Htr'.
  cbn in Htr'.
  step; assumption.
Qed.

Lemma eqtr_zeros_tr_app : 
 forall tr tr', eqtr (zeros +++ tr) (zeros +++ tr').
Proof.
unfold eqtr.
coinduction R H.
intros tr tr'.
rewrite tr_app_unfold.
symmetry.
rewrite tr_app_unfold.
symmetry.
destruct (observe zeros) eqn:?.
- cbn in Heqt.
  inversion Heqt.
- constructor.
  cbn in Heqt.
  inversion Heqt.
  subst.
  apply H.
Qed.

Section Inftr.

Context {A B : Type}.

Variant inftrb (ifr : trace A B -> Prop) : trace' A B -> Prop :=
| Inf_Tcons a b tr (PRED : ifr tr) : inftrb ifr (TconsF a b tr).
Hint Constructors inftrb: core.

Definition inftrb_ ifr : trace A B -> Prop :=
 fun tr => inftrb ifr (observe tr).

Program Definition finftr: mon (trace A B -> Prop) := {| body := inftrb_ |}.
Next Obligation.
  unfold pointwise_relation, Basics.impl, inftrb_.
  intros PX PY PXY Z INF.
  inversion_clear INF; auto.
Qed.

End Inftr.

Definition inftr {A B} := (gfp (@finftr A B)).
#[export] Hint Unfold inftr: core.
#[export] Hint Constructors inftrb: core.

#[export] Instance Proper_iff_inftr {A B} :
 Proper (eqtr ==> iff) (@inftr A B).
Proof.
unfold Proper, respectful, flip, impl; cbn.
intros x y Heq.
split.
- revert x y Heq.
  unfold inftr at 2.
  coinduction R H.
  intros x y Heq Hx.
  apply (gfp_fp feqtr) in Heq.
  inversion Heq; subst.
  * apply (gfp_fp finftr) in Hx.
    inversion Hx; subst.
    congruence.
  * apply (gfp_fp finftr) in Hx.
    inversion Hx; subst.
    rewrite <- H1 in H3.
    inversion H3; subst.
    cbn.
    unfold inftrb_.
    rewrite <- H2.
    constructor.
    eapply H; eauto.
- revert x y Heq.
  unfold inftr at 2.
  coinduction R H.
  intros x y Heq Hy.
  apply (gfp_fp feqtr) in Heq.
  inversion Heq; subst.
  * apply (gfp_fp finftr) in Hy.
    inversion Hy; subst.
    congruence.
  * apply (gfp_fp finftr) in Hy.
    inversion Hy; subst.
    rewrite <- H2 in H3.
    inversion H3; subst.
    cbn.
    unfold inftrb_.
    rewrite <- H1.
    constructor.
    eapply H; eauto.
Qed.

#[export] Instance Proper_flip_impl_inftr {A B} :
 Proper (eqtr ==> flip impl) (@inftr A B).
Proof.
unfold Proper, respectful, flip, impl; cbn.
unfold inftr at 2.
coinduction R H.
intros x y Heqtr Hiftr.
apply (gfp_fp feqtr) in Heqtr.
inversion Heqtr; subst.
- apply (gfp_fp finftr) in Hiftr.
  inversion Hiftr; subst.
  congruence.
- apply (gfp_fp finftr) in Hiftr.
  inversion Hiftr; subst.
  rewrite <- H3 in H2.
  inversion H2; subst.
  cbn.
  unfold inftrb_.
  rewrite <- H1.
  constructor.
  eapply H; eauto.
Qed.

Lemma inftr_Tcons {A B} : forall a b (tr : trace A B),
 inftr (Tcons a b tr) -> inftr tr.
Proof.
unfold inftr.
intros a b tr Htr.
apply (gfp_fp finftr) in Htr.
now inversion Htr; subst.
Qed.

Lemma observe_TnilF_tr_app {A B} : forall a (tr tr' : trace A B),
 observe tr = TnilF a ->
 observe (tr +++ tr') = observe tr'.
Proof.
intros.
cbv in *.
rewrite H; reflexivity.
Qed.

Lemma observe_TconsF_tr_app {A B} : forall a b tr0 (tr tr' : trace A B),
 observe tr = TconsF a b tr0 ->
 observe (tr +++ tr') = observe (Tcons a b (tr0 +++ tr')) .
Proof.
intros.
cbv in *.
rewrite H; reflexivity.
Qed.

Lemma inftr_tr_app {A B} : forall (tr : trace A B),
 inftr tr -> forall tr', inftr (tr' +++ tr).
Proof.
  intros tr INF.
  unfold inftr.
  coinduction R H.
  intros tr'.
  destruct (observe tr') eqn:?.
  - do 3 red; unfold observe; cbn.
    rewrite Heqt.
    apply (gfp_fp finftr) in INF.
    do 3 red in INF. unfold observe in INF.
    inversion INF.
    constructor.
    pose proof gfp_chain R tr0.
    apply H0, PRED.
  - do 3 red; unfold observe; cbn.
    rewrite Heqt; cbn.
    constructor; apply H.
Qed.

Inductive fintr {A B} : trace A B -> Prop :=
| Fin_Tnil : forall a tr,
   observe tr = TnilF a ->
   fintr tr
| Fin_Tcons : forall a b tr tr',
   observe tr = TconsF a b tr' ->
   fintr tr' ->
   fintr tr.
#[export] Hint Constructors fintr : core.

Lemma fintr_Tnil {A B} : forall (a : A),
 @fintr A B (Tnil a).
Proof.
intros; econstructor; eauto.
Qed.
