From Coq Require Import RelationClasses Program.Basics.
From Coinduction Require Import all.

(** * Possibly-infinite traces using negative coinduction *)

(** ** General utility results *)

Import CoindNotations.

Lemma gfp_leq_Chain {X} {L : CompleteLattice X} (b : mon X) (R : Chain b) :
  gfp b <= b ` R.
Proof.
  rewrite <- (gfp_fp b).
  apply b.
  eapply gfp_chain.
Qed.

(** ** Basic trace definitions *)

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

(** ** Basic trace operations *)

Section Operations.

Context {A B : Type}.

Definition tr_hd' (tr : trace' A B) : A :=
match tr with
| TnilF a => a
| TconsF a b tr0 => a
end.

Definition tr_hd : trace A B -> A :=
fun tr => tr_hd' (observe tr).

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

(** ** Trace equality as a bisimulation *)

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

#[export] Instance Proper_eqtr {A B} :
  Proper (eqtr ==> eqtr ==> flip impl) (@eqtr A B).
Proof.
unfold Proper, respectful, flip, impl; cbn.
unfold eqtr; intros.
transitivity y; auto.
symmetry in H0.
transitivity y0; auto.
Qed.

Lemma eqtr_eta_ {A B : Type} (tr : trace A B) : eqtr tr (go (_observe tr)).
Proof. now step. Qed.

Lemma eqtr_eta {A B : Type} (tr : trace A B) : eqtr tr (go (observe tr)).
Proof. now step. Qed.

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

(** ** Validation on infinite trace of zeros *)

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

(** ** Properties of operations *)

Import TraceNotations.

Lemma tr_hd_unfold {A B} :
 forall (tr : trace A B),
  tr_hd tr = (match observe tr with
              | TnilF a => a
              | TconsF a b tr' => a
              end).
Proof.
intros tr; unfold tr_hd.
destruct (observe tr) eqn:?; reflexivity.
Qed.

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

Lemma eqtr_hd {A B : Type} (tr1 tr2 : trace A B) :
 eqtr tr1 tr2 -> tr_hd tr1 = tr_hd tr2.
Proof.
unfold eqtr; intros Heq.
apply (gfp_fp feqtr) in Heq.
cbn in Heq.
rewrite 2 tr_hd_unfold.
destruct (observe tr1) eqn:?;
 destruct (observe tr2) eqn:?.
- inversion Heq; subst; reflexivity.
- inversion Heq.
- inversion Heq.
- inversion Heq; subst; reflexivity.
Qed.

Lemma eqtr_Tnil_tr_app {A B} : forall a (tr : trace A B), eqtr (Tnil a +++ tr) tr.
Proof.
intros a tr.
rewrite tr_app_unfold.
reflexivity.
Qed.

Lemma eqtr_left_Tnil_tr_app {A B} :
forall a (tr1 tr2 : trace A B),
 eqtr (Tnil a +++ tr1) (Tnil a +++ tr2) ->
 eqtr tr1 tr2.
Proof.
intros a tr1 tr2.
rewrite 2 tr_app_unfold.
auto.
Qed.

Lemma eqtr_left_tr_app_Tnil {A B} :
forall a (tr1 tr2 : trace A B),
 eqtr tr1 tr2 ->
 eqtr (Tnil a +++ tr1) (Tnil a +++ tr2).
Proof.
intros a tr1 tr2.
rewrite 2 tr_app_unfold.
auto.
Qed.

Lemma eqtr_Tcons_tr_app {A B} : forall a b (tr tr' : trace A B),
 eqtr (Tcons a b tr +++ tr') (Tcons a b (tr +++ tr')).
Proof.
intros a b tr tr'.
rewrite tr_app_unfold.
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

(** ** Infinite trace definitions *)

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

#[export] Instance inftr_upto_eqtr {A B} {R : Chain (@finftr A B)} :
 Proper (eqtr ==> flip impl) (` R).
Proof.
  apply tower.
  - unfold Proper, respectful.
    apply inf_closed_all; intros ?.
    apply inf_closed_all; intros ?.
    apply inf_closed_impl.
    now intros ???.
    apply inf_closed_impl.
    now intros ???.
    now intros ??.
  - clear R; intros R HP tr tr' EQ INF.
    apply (gfp_fp feqtr) in EQ.
    cbn in *; red in INF |- *.
    inversion EQ.
    + rewrite <- H in INF; inversion INF.
    + constructor.
      rewrite <- H in INF; inversion INF; subst.
      eapply HP; eauto.
Qed.

#[export] Instance Proper_inftr {A B} :
 Proper (eqtr ==> flip impl) (@inftr A B).
Proof. typeclasses eauto. Qed.

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

(** ** Infinite trace properties *)

Lemma inftr_Tcons {A B} : forall a b (tr : trace A B),
 inftr (Tcons a b tr) -> inftr tr.
Proof.
unfold inftr.
intros a b tr Htr.
apply (gfp_fp finftr) in Htr.
now inversion Htr; subst.
Qed.

Lemma inftr_tr_app {A B} : forall (tr : trace A B),
 inftr tr -> forall tr', inftr (tr' +++ tr).
Proof.
  intros tr INF.
  unfold inftr.
  coinduction R H.
  intros tr'.
  rewrite tr_app_unfold.
  destruct (observe tr') eqn:?.
  - now eapply (gfp_leq_Chain finftr).
  - constructor; apply H.
Qed.

Lemma tr_app_inftr {A B} : forall (tr : trace A B),
 inftr tr -> forall tr', inftr (tr +++ tr').
Proof.
  unfold inftr at 2.
  coinduction R H.
  intros tr Hinf tr'.
  apply (gfp_fp finftr) in Hinf.
  inversion Hinf.
  rewrite tr_app_unfold.
  rewrite <- H1.
  constructor.
  apply H.
  apply (gfp_fp finftr) in PRED.
  now apply (gfp_fp finftr).
Qed.

(** ** Finite trace definitions *)

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
Proof. intros; econstructor; eauto. Qed.

#[export] Instance Proper_fintr {A B} :
 Proper (eqtr ==> flip impl) (@fintr A B).
Proof.
unfold Proper, respectful, flip, impl; cbn.
intros x y Heq Hy.
apply (gfp_fp feqtr) in Heq.
revert Hy x Heq.
induction 1.
- intros x Heq.
  inversion Heq; subst; [|congruence].
  symmetry in H1.
  revert H1.
  apply Fin_Tnil.
- intros x Heq.
  inversion Heq; subst; [congruence|].
  rewrite <- H2 in H.
  inversion H; subst; clear H.
  symmetry in H1.
  apply (Fin_Tcons H1).
  apply IHHy.
  now apply (gfp_fp feqtr) in REL.
Qed.

(** ** Finite trace properties *)

Lemma invert_fintr_delay {A B} : forall a b (tr : trace A B) (h : fintr (Tcons a b tr)), fintr tr.
Proof.
intros a b tr h; inversion h; cbn in H.
- congruence.
- now inversion H; subst.
Qed.

Lemma fintr_inftr_not {A B} : forall(tr : trace A B),
 fintr tr -> inftr tr -> False.
Proof.
intros tr; induction 1; intros Hinf.
- apply (gfp_fp finftr) in Hinf.
  inversion Hinf; subst.
  congruence.
- apply (gfp_fp finftr) in Hinf.
  inversion Hinf; subst.
  rewrite H in H2.
  inversion H2; subst.
  apply IHfintr.
  now apply (gfp_fp finftr).
Qed.

Lemma not_fintr_inftr {A B} : forall(tr : trace A B),
 ~ fintr tr -> inftr tr.
Proof.
unfold inftr.
coinduction R H.
intros tr Hfin.
destruct (observe tr) eqn:?.
- contradict Hfin.
  revert Heqt.
  apply Fin_Tnil.
- cbn.
  unfold inftrb_.
  rewrite Heqt.
  constructor.
  apply H.
  intros Hf.
  contradict Hfin.
  revert Heqt Hf.
  apply Fin_Tcons.
Qed.

(** * Final element properties *)

Inductive finaltr {A B} : trace A B -> A -> Prop :=
| Final_Tnil : forall a,
   finaltr (Tnil a) a
| Final_Tcons : forall a b a' tr,
   finaltr tr a' ->
   finaltr (Tcons a b tr) a'.

Fail Fixpoint final {A B} (tr : trace A B) (h : fintr tr) {struct h} : A :=
match observe tr as tr' return (fintr (go tr') -> A) with
| TnilF a => fun _ => a
| TconsF a b tr => fun h0 => final (invert_fintr_delay h0)
end h.