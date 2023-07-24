From Coq Require Import RelationClasses Program.Basics.
From Coinduction Require Import all.
From NegativeTraces Require Import Traces.

Import CoindNotations.

Local Open Scope trace_scope.

CoInductive eq_tr_pr {A B} (tr1 tr2 : trace A B) : Prop :=
{ _obs_eq_tr_pr : eq_tr'_b eq_tr_pr (observe tr1) (observe tr2) }.

Lemma eq_tr_pr_gfp {A B} :
 forall (R : relation (@trace A B)),
   (forall tr1 tr2, R tr1 tr2 -> eq_tr'_b R (observe tr1) (observe tr2)) ->
     (forall tr1 tr2, R tr1 tr2 -> eq_tr_pr tr1 tr2).
Proof.
intros R HR.
cofix CH.
intros tr1 tr2 H; constructor.
apply HR in H.
inversion H.
- constructor.
- constructor.
  now apply CH.
Qed.

Lemma eq_tr_eq_tr_pr {A B} : forall (tr1 tr2 : trace A B),
 eq_tr tr1 tr2 -> eq_tr_pr tr1 tr2.
Proof.
apply eq_tr_pr_gfp.
intros tr1 tr2 Heq.
apply (gfp_fp eq_tr_f) in Heq.
inversion Heq.
- constructor.
- now constructor.
Qed.

Lemma eq_tr_pr_eq_tr {A B} : forall (tr1 tr2 : trace A B),
 eq_tr_pr tr1 tr2 -> eq_tr tr1 tr2.
Proof.
unfold eq_tr.
coinduction R H.
intros tr1 tr2 Hpr.
inversion Hpr as [Hobs].
inversion Hobs; cbn.
- rewrite <- H1, <- H2.
  constructor.
- rewrite <- H1, <- H2.
  constructor.
  now apply H.
Qed.
