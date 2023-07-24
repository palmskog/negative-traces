From Coq Require Import RelationClasses Program.Basics.
From Coinduction Require Import all.

(** * Possibly-infinite traces using negative coinduction *)

(** ** General utility results *)

Import CoindNotations.

Lemma gfp_bchain {X} {L : CompleteLattice X} (b : mon X) (x : Chain b) :
  gfp b <= b ` x.
Proof. apply (gfp_chain (chain_b x)). Qed.

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
#[local] Open Scope trace_scope.

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

Definition hd_tr' (tr : trace' A B) : A :=
match tr with
| TnilF a => a
| TconsF a b tr0 => a
end.

Definition hd_tr : trace A B -> A :=
fun tr => hd_tr' (observe tr).

Definition app_tr' (tr' : trace A B) : trace' A B -> trace A B :=
 cofix app_tr'_ (tr : trace' A B) :=
 match tr with
  | TnilF a => tr'
  | TconsF a b tr0 => Tcons a b (app_tr'_ (observe tr0) )
  end.

Definition app_tr : trace A B -> trace A B -> trace A B :=
 fun tr tr' => app_tr' tr' (observe tr).

End Operations.

Module TraceNotations.
Infix "+++" := app_tr (at level 60, right associativity) : trace_scope.
End TraceNotations.

(** ** Trace equality as a bisimulation *)

Section Eq.

Context {A B : Type}.

Variant eq_tr'_b (eq : trace A B -> trace A B -> Prop) :
 trace' A B -> trace' A B -> Prop :=
| Eq_Tnil a : eq_tr'_b eq (TnilF a) (TnilF a)
| Eq_Tcons a b tr1 tr2 (REL : eq tr1 tr2) :
   eq_tr'_b eq (TconsF a b tr1) (TconsF a b tr2).

Hint Constructors eq_tr'_b : core.

Definition eq_tr_b eq : trace A B -> trace A B -> Prop :=
 fun tr1 tr2 => eq_tr'_b eq (observe tr1) (observe tr2).

Program Definition eq_tr_f : mon (trace A B -> trace A B -> Prop) :=
 {| body := eq_tr_b |}.
Next Obligation.
unfold pointwise_relation, Basics.impl, eq_tr_b.
intros ?? INC ?? EQ. inversion_clear EQ; auto.
Qed.

End Eq.

Definition eq_tr {A B} := (gfp (@eq_tr_f A B)).

#[export] Hint Unfold eq_tr : core.
#[export] Hint Constructors eq_tr'_b : core.
Arguments eq_tr_b _ _/.

Ltac fold_eq_tr :=
  repeat
    match goal with
    | h: context[@eq_tr_f ?A ?B] |- _ => fold (@eq_tr A B) in h
    | |- context[@eq_tr_f ?A ?B] => fold (@eq_tr A B)
    end.

#[export] Instance Reflexive_eq_tr'_b {A B} {R} {Hr: Reflexive R} :
 Reflexive (@eq_tr'_b A B R).
Proof. now intros [a|a b tr]; constructor. Qed.

#[export] Instance Reflexive_eq_tr_f {A B} :
 forall {R: Chain (@eq_tr_f A B)}, Reflexive `R.
Proof. apply Reflexive_chain. now cbn. Qed.

#[export] Instance Symmetric_eq_tr'_b {A B} {R} {Hr: Symmetric R} :
 Symmetric (@eq_tr'_b A B R).
Proof.
intros [a|a b tr]; intros [a'|a' b' tr'] Heq; try inversion Heq.
- constructor.
- constructor; now symmetry.
Qed.

#[export] Instance Symmetric_eq_tr_f {A B} :
 forall {R: Chain (@eq_tr_f A B)}, Symmetric `R.
Proof.
apply Symmetric_chain.
intros R HR x y xy.
now apply Symmetric_eq_tr'_b.
Qed.

#[export] Instance Transitive_eq_tr'_b {A B} {R} {Hr: Transitive R} :
 Transitive (@eq_tr'_b A B R).
Proof.
intros [xa|xa xb xtr]; intros [ya|ya yb ytr]; intros [za|za zb ztr] Heqx Heqy;
 try now inversion Heqx.
inversion Heqx; subst.
inversion Heqy; subst.
constructor; revert REL REL0; apply Hr.
Qed.

#[export] Instance Transitive_eq_tr_f {A B : Type} :
 forall {R: Chain (@eq_tr_f A B)}, Transitive `R.
Proof.
apply Transitive_chain. 
intros R HR.
intros x y z.
now apply Transitive_eq_tr'_b.
Qed.

#[export] Instance Equivalence_eq_tr {A B}: Equivalence (@eq_tr A B).
Proof. split; typeclasses eauto. Qed.

#[export] Instance Proper_eq_tr {A B} :
 Proper (eq_tr ==> eq_tr ==> flip impl) (@eq_tr A B).
Proof.
unfold Proper, respectful, flip, impl; cbn.
unfold eq_tr; intros.
transitivity y; auto.
symmetry in H0.
transitivity y0; auto.
Qed.

Lemma eq_tr_eta_ {A B} (tr : trace A B) : eq_tr tr (go (_observe tr)).
Proof. now step. Qed.

Lemma eq_tr_eta {A B} (tr : trace A B) : eq_tr tr (go (observe tr)).
Proof. now step. Qed.

Lemma eq_tr_Tnil_inv {A B} (a1 a2 : A) :
 @eq_tr A B (Tnil a1) (Tnil a2) ->
 a1 = a2.
Proof.
unfold eq_tr; intros Heq.
apply (gfp_fp eq_tr_f) in Heq.
cbn in Heq.
inversion Heq; subst.
reflexivity.
Qed.

Lemma eqtr_Tcons_inv {A B} a1 a2 b1 b2 (tr1 tr2 : trace A B) :
 eq_tr (Tcons a1 b1 tr1) (Tcons a2 b2 tr2) ->
 a1 = a2 /\ b1 = b2 /\ eq_tr tr1 tr2.
Proof.
unfold eq_tr; intros Heq.
apply (gfp_fp eq_tr_f) in Heq.
cbn in Heq.
inversion Heq; subst.
tauto.
Qed.

(** ** Validation on infinite trace of zeros *)

CoFixpoint zeros : trace nat unit := Tcons 0 tt zeros.
Definition zeros' : trace nat unit := Tcons 0 tt (Tcons 0 tt zeros).

Example zeros_zeros_eq_tr : eq_tr zeros zeros.
Proof. reflexivity. Qed.

Example zeros_zeros_one_eq_tr : eq_tr zeros (Tcons 0 tt zeros).
Proof. unfold eq_tr; step; cbn; reflexivity. Qed.

Example zeros_zeros'_eqtr : eq_tr zeros zeros'.
Proof.
unfold eq_tr, zeros'.
step; cbn; constructor; cbn.
apply zeros_zeros_one_eq_tr.
Qed.

(** ** Properties of operations *)

Import TraceNotations.

Lemma observe_TnilF_app_tr {A B} : forall a (tr tr' : trace A B),
 observe tr = TnilF a ->
 observe (tr +++ tr') = observe tr'.
Proof. cbv; intros; rewrite H; reflexivity. Qed.

Lemma observe_TconsF_app_tr {A B} : forall a b tr0 (tr tr' : trace A B),
 observe tr = TconsF a b tr0 ->
 observe (tr +++ tr') = observe (Tcons a b (tr0 +++ tr')) .
Proof. cbv; intros; rewrite H; reflexivity. Qed.

Lemma hd_tr_unfold {A B} :
 forall (tr : trace A B),
  hd_tr tr = (match observe tr with
              | TnilF a => a
              | TconsF a b tr' => a
              end).
Proof.
intros tr; unfold hd_tr.
destruct (observe tr) eqn:?; reflexivity.
Qed.

Lemma app_tr_unfold {A B} :
  forall (tr tr' : trace A B),
    eq_tr (tr +++ tr')
      (match observe tr with
       | TnilF a => tr'
       | TconsF a b tr0 => Tcons a b (tr0 +++ tr')
       end).
Proof. intros; now step. Qed.

Lemma eq_tr_hd {A B} (tr1 tr2 : trace A B) :
 eq_tr tr1 tr2 -> hd_tr tr1 = hd_tr tr2.
Proof.
unfold eq_tr; intros Heq.
apply (gfp_fp eq_tr_f) in Heq.
cbn in Heq.
rewrite 2 hd_tr_unfold.
destruct (observe tr1) eqn:?;
 destruct (observe tr2) eqn:?.
- inversion Heq; subst; reflexivity.
- inversion Heq.
- inversion Heq.
- inversion Heq; subst; reflexivity.
Qed.

Lemma eq_tr_Tnil_app_tr {A B} : forall a (tr : trace A B),
 eq_tr (Tnil a +++ tr) tr.
Proof.
intros a tr.
rewrite app_tr_unfold.
reflexivity.
Qed.

Lemma eq_tr_Tcons_app_tr {A B} : forall a b (tr tr' : trace A B),
 eq_tr (Tcons a b tr +++ tr') (Tcons a b (tr +++ tr')).
Proof.
intros a b tr tr'.
rewrite app_tr_unfold.
reflexivity.
Qed.

Lemma eq_tr_left_Tnil_app_tr {A B} :
forall a (tr1 tr2 : trace A B),
 eq_tr (Tnil a +++ tr1) (Tnil a +++ tr2) ->
 eq_tr tr1 tr2.
Proof.
intros a tr1 tr2.
rewrite 2 app_tr_unfold.
auto.
Qed.

Lemma eq_tr_left_app_tr_Tnil {A B} :
forall a (tr1 tr2 : trace A B),
 eq_tr tr1 tr2 ->
 eq_tr (Tnil a +++ tr1) (Tnil a +++ tr2).
Proof.
intros a tr1 tr2.
rewrite 2 app_tr_unfold.
auto.
Qed.

Lemma eq_tr_tr_app_left {A B} :
forall (tr11 tr12 tr : trace A B),
 eq_tr tr11 tr12 ->
 eq_tr (tr11 +++ tr) (tr12 +++ tr).
Proof.
unfold eq_tr at 2.
coinduction R H; intros tr11 tr12 tr Heq.
apply (gfp_fp eq_tr_f) in Heq.
rewrite app_tr_unfold.
symmetry.
rewrite app_tr_unfold.
symmetry.
inversion Heq; auto.
constructor.
apply H, REL.
Qed.

Lemma eq_tr_app_tr {A B} : forall (tr1 tr2 tr3 tr4 : trace A B), 
 eq_tr tr1 tr2 ->
 eq_tr tr3 tr4 ->
 eq_tr (tr1 +++ tr3) (tr2 +++ tr4).
Proof.
unfold eq_tr at 3.
coinduction R H; intros tr1 tr2 tr3 tr4 Htr Htr'.
apply (gfp_fp eq_tr_f) in Htr.
rewrite app_tr_unfold.
symmetry.
rewrite app_tr_unfold.
symmetry.
inversion Htr; auto.
- rewrite Htr'; reflexivity.
- constructor.
  apply H; [assumption|].
  apply (gfp_fp eq_tr_f) in Htr'.
  cbn in Htr'.
  step; assumption.
Qed.

Lemma eqtr_zeros_tr_app : 
 forall tr tr', eq_tr (zeros +++ tr) (zeros +++ tr').
Proof.
unfold eq_tr.
coinduction R H.
intros tr tr'.
rewrite app_tr_unfold.
symmetry.
rewrite app_tr_unfold.
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

Section Inf.

Context {A B : Type}.

Variant inf_tr'_b (inf : trace A B -> Prop) : trace' A B -> Prop :=
| Inf_Tcons a b tr (PRED : inf tr) : inf_tr'_b inf (TconsF a b tr).
Hint Constructors inf_tr'_b : core.

Definition inf_tr_b inf : trace A B -> Prop :=
 fun tr => inf_tr'_b inf (observe tr).

Program Definition inf_tr_f : mon (trace A B -> Prop) :=
 {| body := inf_tr_b |}.
Next Obligation.
  unfold pointwise_relation, Basics.impl, inf_tr_b.
  intros PX PY PXY Z INF.
  inversion_clear INF; auto.
Qed.

End Inf.

Definition inf_tr {A B} := (gfp (@inf_tr_f A B)).

#[export] Hint Unfold inf_tr : core.
#[export] Hint Constructors inf_tr'_b : core.

#[export] Instance inf_tr_upto_eq_tr {A B} {R : Chain (@inf_tr_f A B)} :
 Proper (eq_tr ==> flip impl) (` R).
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
   apply (gfp_fp eq_tr_f) in EQ.
   cbn in *; red in INF |- *.
   inversion EQ.
   + rewrite <- H in INF; inversion INF.
   + constructor.
     rewrite <- H in INF; inversion INF; subst.
     eapply HP; eauto.
Qed.

#[export] Instance Proper_inf_tr {A B} :
 Proper (eq_tr ==> flip impl) (@inf_tr A B).
Proof. typeclasses eauto. Qed.

#[export] Instance Proper_iff_inf_tr {A B} :
 Proper (eq_tr ==> iff) (@inf_tr A B).
Proof.
unfold Proper, respectful, flip, impl; cbn.
intros x y Heq; split; now rewrite Heq.
Qed.

(** ** Infinite trace properties *)

Lemma inf_tr_Tcons {A B} : forall a b (tr : trace A B),
 inf_tr (Tcons a b tr) -> inf_tr tr.
Proof.
unfold inf_tr.
intros a b tr Htr.
apply (gfp_fp inf_tr_f) in Htr.
now inversion Htr; subst.
Qed.

Lemma inf_tr_app_tr {A B} : forall (tr : trace A B),
 inf_tr tr -> forall tr', inf_tr (tr' +++ tr).
Proof.
intros tr INF.
unfold inf_tr.
coinduction R H.
intros tr'.
rewrite app_tr_unfold.
destruct (observe tr') eqn:?.
- now apply (gfp_bchain inf_tr_f).
- constructor; apply H.
Qed.

Lemma app_tr_inf_tr {A B} : forall (tr : trace A B),
 inf_tr tr -> forall tr', inf_tr (tr +++ tr').
Proof.
unfold inf_tr at 2.
coinduction R H.
intros tr Hinf tr'.
apply (gfp_fp inf_tr_f) in Hinf.
inversion Hinf.
rewrite app_tr_unfold.
rewrite <- H1.
constructor.
apply H.
apply (gfp_fp inf_tr_f) in PRED.
now apply (gfp_fp inf_tr_f).
Qed.

(** ** Finite trace definitions *)

Inductive fin_tr' {A B} : trace' A B -> Prop :=
| Fin_Tnil : forall a,
   fin_tr' (TnilF a)
| Fin_Tcons : forall a b tr,
   fin_tr' (observe tr) ->
   fin_tr' (TconsF a b tr).

#[export] Hint Constructors fin_tr' : core.
Arguments Fin_Tnil {A B} a.

Definition fin_tr {A B} : trace A B -> Prop :=
 fun tr => fin_tr' (observe tr).

(** ** Finite trace properties *)

Lemma fin_tr_Tnil {A B} : forall (a : A),
 @fin_tr A B (Tnil a).
Proof. intros a; constructor. Qed.

Lemma inv_TconsF_fin_tr' {A B} (a : A) (b : B) (tr : trace A B)
 (h : fin_tr' (TconsF a b tr)) : fin_tr' (observe tr).
Proof. now inversion h. Defined.

#[export] Instance Proper_fin_tr {A B} :
 Proper (eq_tr ==> flip impl) (@fin_tr A B).
Proof.
unfold Proper, respectful, flip, impl; cbn.
intros x y Heq Hy.
unfold fin_tr in Hy.
symmetry in Heq.
rewrite eq_tr_eta in Heq.
revert x Heq.
induction Hy.
- intros x Heq.
  apply (gfp_fp eq_tr_f) in Heq.
  inversion Heq.
  unfold fin_tr.
  rewrite <- H.
  constructor.
- intros x Heq.
  apply (gfp_fp eq_tr_f) in Heq.
  inversion Heq; subst.
  unfold fin_tr.
  rewrite <- H.
  apply Fin_Tcons.
  apply IHHy.
  now rewrite <- eq_tr_eta.
Qed.

Lemma fin_tr_inf_tr_not {A B} : forall (tr : trace A B),
 fin_tr tr -> inf_tr tr -> False.
Proof.
unfold fin_tr,inf_tr.
intros tr Hfin Hinf.
apply (gfp_fp inf_tr_f) in Hinf.
cbn in Hinf.
unfold inf_tr_b in Hinf.
revert Hfin Hinf.
induction 1; intros Hinf.
- inversion Hinf.
- apply IHHfin; clear IHHfin.
  inversion Hinf; subst.
  now apply (gfp_fp inf_tr_f) in PRED.
Qed.

Lemma not_fin_tr_inf_tr {A B} : forall(tr : trace A B),
 ~ fin_tr tr -> inf_tr tr.
Proof.
unfold inf_tr.
coinduction R H.
intros tr Hfin.
destruct (observe tr) eqn:?.
- contradict Hfin.
  unfold fin_tr.
  rewrite Heqt.
  apply Fin_Tnil.
- cbn.
  unfold inf_tr_b.
  rewrite Heqt.
  constructor.
  apply H.
  intros Hf.
  contradict Hfin.  
  unfold fin_tr.
  rewrite Heqt.
  now apply Fin_Tcons.
Qed.

(** * Final element properties *)

Inductive final_tr' {A B} : trace' A B -> A -> Prop :=
| Final_Tnil : forall a,
   final_tr' (TnilF a) a
| Final_Tcons : forall a b a' tr,
   final_tr' (observe tr) a' ->
   final_tr' (TconsF a b tr) a'.

#[export] Hint Constructors final_tr' : core.
Arguments Final_Tnil {A B} a.

Definition final_tr {A B} : trace A B -> A -> Prop :=
 fun tr => final_tr' (observe tr).

Definition final' {A B} : forall (tr: trace' A B), fin_tr' tr -> A :=
 fix F (tr : trace' A B) (h : fin_tr' tr) {struct h} : A :=
  match tr as tr' return (fin_tr' tr' -> A) with
  | TnilF a => fun _ => a
  | TconsF a b tr0 => fun h => F (observe tr0) (inv_TconsF_fin_tr' h)
  end h.

Definition final {A B} (tr : trace A B) (h : fin_tr tr) : A :=
 final' h.

Lemma final_tr_fin_tr {A B} : forall (tr : trace A B) a,
 final_tr tr a -> fin_tr tr.
Proof.
refine (fix IH tr a h {struct h} := _).
unfold final_tr in h.
unfold fin_tr.
inversion h; subst.
- apply Fin_Tnil.
- apply Fin_Tcons.
  now apply (IH _ a).
Qed.

Lemma fin_tr_final_tr {A B} : forall (tr : trace A B) (h : fin_tr tr),
 final_tr tr (final h).
Proof.
refine (fix IH tr h {struct h} := _).
unfold fin_tr in h.
unfold final_tr, final, final'.
inversion h; subst.
- dependent inversion h; auto.
  congruence.
- dependent inversion h; auto.
  rewrite <- H2 in H.
  inversion H; subst.
  apply Final_Tcons.
  apply IH.
Qed.

Lemma final_tr_hd_app_tr {A B} : forall (tr0 : trace A B) a,
 final_tr tr0 a ->
 forall tr1, hd_tr tr1 = a ->
 hd_tr (tr0 +++ tr1) = hd_tr tr0.
Proof.
refine (fix IH tr a h {struct h} := _).
inversion h; subst.
- unfold hd_tr.
  symmetry in H0.
  intros tr1 Hhd.
  rewrite (observe_TnilF_app_tr _ _ H0).
  now rewrite H0.
- unfold hd_tr.
  intros tr1 Hhd.
  symmetry in H.
  rewrite (observe_TconsF_app_tr _ _ H).
  now rewrite H.
Qed.

(** * Basic predicates *)

Definition tt_tr' {A B} : trace' A B -> Prop :=
 fun _ => True.

Definition tt_tr {A B} : trace A B -> Prop :=
 fun tr => tt_tr' (observe tr).

#[export] Instance Proper_tt_tr {A B} :
 Proper (eq_tr ==> flip impl) (@tt_tr A B).
Proof. now cbn. Qed.

Definition ff_tr' {A B} : trace' A B -> Prop :=
 fun _ => False.

Definition ff_tr {A B} : trace A B -> Prop :=
 fun tr => ff_tr' (observe tr).

#[export] Instance Proper_tr_ff {A B} :
 Proper (eq_tr ==> flip impl) (@ff_tr A B).
Proof. now cbn. Qed.

Definition singleton_tr' {A B} (u : A -> Prop) (tr : trace' A B) : Prop :=
 exists a, u a /\ eq_tr (go tr) (Tnil a).

Definition singleton_tr {A B} (u : A -> Prop) : trace A B -> Prop :=
 fun tr => singleton_tr' u (observe tr).

#[export] Instance Proper_singleton_tr {A B} (u : A -> Prop) :
 Proper (eq_tr ==> flip impl) (@singleton_tr A B u).
Proof. 
unfold Proper, respectful, flip, impl; cbn.
unfold singleton_tr, eq_tr.
intros x y Heq.
apply (gfp_fp eq_tr_f) in Heq.
inversion Heq; auto.
intros [a0 [Hu Heq']].
apply (gfp_fp eq_tr_f) in Heq'.
inversion Heq'.
Qed.

(** * Follows relation *)

Section Follows.

Context {A B : Type}.

Variant follows_tr'_b (p : trace A B -> Prop) (fol : trace A B -> trace A B -> Prop) :
 trace' A B -> trace' A B -> Prop :=
| Follows_Tnil : forall a b tr, p tr ->
   follows_tr'_b p fol (TnilF a) (TconsF a b tr)
| Follows_Tcons : forall a b tr tr' (REL : fol tr tr'),
   follows_tr'_b p fol (TconsF a b tr) (TconsF a b tr').

Hint Constructors follows_tr'_b : core.

Definition follows_tr_b p ftr : trace A B -> trace A B -> Prop :=
 fun tr1 tr2 => follows_tr'_b p ftr (observe tr1) (observe tr2).

Program Definition follows_tr_f p : mon (trace A B -> trace A B -> Prop) :=
 {| body := follows_tr_b p |}.
Next Obligation.
  unfold pointwise_relation, Basics.impl, follows_tr_b.
  intros PX PY PXY tr tr' FL.
  inversion_clear FL; auto.
Qed.

End Follows.

Definition follows_tr {A B} p := (gfp (@follows_tr_f A B p)).

#[export] Hint Unfold follows_tr : core.
#[export] Hint Constructors follows_tr'_b : core.
Arguments follows_tr_b _ _ _/.

#[export] Instance Proper_follows_tr {A B} p (Hp : Proper (eq_tr ==> flip impl) p) :
  Proper (eq_tr ==> eq_tr ==> flip impl) (@follows_tr A B p).
Proof.
unfold Proper, respectful, flip, impl; cbn.
unfold follows_tr at 2.
coinduction R H.
unfold follows_tr; intros x y Heq x' y' Heq' Hf.
apply (gfp_fp (follows_tr_f p)) in Hf.
cbn in Hf.
unfold eq_tr in Heq.
apply (gfp_fp eq_tr_f) in Heq.
apply (gfp_fp eq_tr_f) in Heq'.
cbn in Heq, Heq'.
inversion Heq.
- rewrite <- H2 in Hf.
  inversion Hf; subst.
  rewrite <- H3 in Heq'.
  symmetry in Heq'.
  inversion Heq'; subst.
  cbn.
  rewrite <- H1, <- H8.
  constructor.
  symmetry in REL.
  now apply (Hp _ _ REL).
- rewrite <- H2 in Hf.
  inversion Hf; subst.
  rewrite <- H6 in Heq'.
  symmetry in Heq'.
  inversion Heq'; subst.
  cbn.
  rewrite <- H1, <- H7.
  constructor.
  apply (H tr1 tr2 REL tr3 tr').  
  * now symmetry.
  * apply REL0.
Qed.

Definition append_tr' {A B} (p1 p2 : trace A B -> Prop) : trace' A B -> Prop :=
fun tr => exists tr', p1 tr' /\ follows_tr p2 tr' (go tr).

Definition append_tr {A B} (p1 p2 : trace A B -> Prop) : trace A B -> Prop :=
fun tr => append_tr' p1 p2 (observe tr).

(*
Lemma appendtr_assoc_L {A B} : forall p1 p2 p3 (tr : trace A B),
 (appendtr (appendtr p1 p2) p3) tr -> appendtr p1 (appendtr p2 p3) tr.
Proof.
Abort.
*)
