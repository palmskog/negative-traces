Set Implicit Arguments.
Set Contextual Implicit.
Set Primitive Projections.

Section Trace.

Context {A B : Type}.

Inductive traceF (X : Type) : Type :=
| TnilF : A -> traceF X
| TconsF : A -> B -> X -> traceF X.

CoInductive trace := gotrace { untrace : traceF trace }.

End Trace.

Arguments trace _ _ : clear implicits.
Arguments traceF _ _ : clear implicits.

Notation trace' A B := (traceF A B (trace A B)).

Definition observe {A B} (tr : trace A B) : trace' A B := @untrace A B tr.

Notation Tnil a := (gotrace (TnilF a)).
Notation Tcons a b tr := (gotrace (TconsF a b tr)).

Section Operations.

Variables A B : Type.

Definition hd (tr : trace A B) : A :=
match observe tr with
| TnilF a => a
| TconsF a b tr0 => a
end.

CoFixpoint trace_append (tr tr' : trace A B) : trace A B :=
match observe tr with
| TnilF _ => tr'
| TconsF a b tr0 => Tcons a b (trace_append tr' tr0)
end.

#[local] Infix "+++" := trace_append (at level 60, right associativity).

End Operations.

From Paco Require Import paco.

Section Eqtr.

Context {A B : Type}.

Inductive eqtrF (sim : trace A B -> trace A B -> Prop) :
    trace' A B -> trace' A B -> Prop :=
| EqTrTnilF a :
   eqtrF sim (TnilF a) (TnilF a)
| EqTrTconsF a b tr1 tr2 (REL : sim tr1 tr2) :
  eqtrF sim (TconsF a b tr1) (TconsF a b tr2).

Definition eqtr_ sim : trace A B -> trace A B -> Prop :=
  fun tr1 tr2 => eqtrF sim (observe tr1) (observe tr2).

Lemma eqtrF_mono sim sim' tr tr'
 (IN: eqtrF sim tr tr')
 (LE: sim <2= sim') :
 eqtrF sim' tr tr'.
Proof.
intros. induction IN.
- apply EqTrTnilF.
- apply EqTrTconsF.
  apply LE.
  apply REL.
Qed.

Lemma eqtr__mono : monotone2 eqtr_.
Proof.
do 2 red. intros.
eapply eqtrF_mono; eauto.
Qed.

Hint Resolve eqtr__mono : paco.

Definition eqtr : trace A B -> trace A B -> Prop :=
  paco2 eqtr_ bot2.

Inductive eqtr_trans_clo (r : trace A B -> trace A B -> Prop)
  : trace A B -> trace A B -> Prop :=
| eqtr_trans_clo_intro tr1 tr2 tr1' tr2'
      (EQVl: eqtr tr1 tr1')
      (EQVr: eqtr tr2 tr2')
      (REL: r tr1' tr2')
  : eqtr_trans_clo r tr1 tr2.

Definition eqtrC := eqtr_trans_clo.

End Eqtr.

Require Import Program.Tactics.

Ltac unfold_eqtr :=
  (try match goal with [|- eqtr_ _ _ _] => red end);
  (repeat match goal with [H: eqtr_ _ _ _ |- _ ] => red in H end).

Tactic Notation "hinduction" hyp(IND) "before" hyp(H)
  := move IND before H; revert_until IND; induction IND.

Ltac inv H := inversion H; clear H; subst.

Section EqTrProps.

Context {A B : Type}.

Lemma eqtrC_mon r1 r2 t1 t2
      (IN: eqtrC r1 t1 t2)
      (LE: r1 <2= r2):
  @eqtrC A B r2 t1 t2.
Proof.
  destruct IN. econstructor; eauto.
Qed.

Hint Resolve eqtrC_mon : paco.

Lemma eqtrC_wcompat :
  wcompatible2 (@eqtr_ A B) eqtrC.
Proof.
  econstructor; [ eauto with paco | ].
  intros. destruct PR.
  punfold EQVl. punfold EQVr. unfold_eqtr.
  hinduction REL before r; intros; clear tr1' tr2'.
  - remember (TnilF a) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; eauto.
    remember (TnilF a0) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy.
    constructor.
  - remember (TauF m1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; [ | eauto with itree ].
    remember (TauF m3) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; [ | eauto with itree ].
    pclearbot. econstructor. gclo.
    econstructor; eauto with paco.
  - remember (VisF e k1) as x.
    hinduction EQVl before r; intros; try discriminate Heqx; [ inv_Vis | eauto with itree ].
    remember (VisF e k3) as y.
    hinduction EQVr before r; intros; try discriminate Heqy; [ inv_Vis | eauto with itree ].
    econstructor. intros. pclearbot.
    eapply MON.
    + apply CMP. econstructor...
    + intros. apply gpaco2_clo, PR.
  - remember (TauF t1) as x.
    hinduction EQVl before r; intros; subst; try inv Heqx; try inv CHECK; [ | eauto with itree ].
    pclearbot. punfold REL...
  - remember (TauF t2) as y.
    hinduction EQVr before r; intros; subst; try inv Heqy; try inv CHECK; [ | eauto with itree ].
    pclearbot. punfold REL...
Qed.

Hint Resolve eqitC_wcompat : paco.

Lemma eqit_idclo_compat b1 b2: compose (eqitC b1 b2) id <3= compose id (eqitC b1 b2).
Proof.
  intros. apply PR.
Qed.
Hint Resolve eqit_idclo_compat : paco.

Lemma eqitC_dist b1 b2:
  forall r1 r2, eqitC b1 b2 (r1 \2/ r2) <2= (eqitC b1 b2 r1 \2/ eqitC b1 b2 r2).
Proof.
  intros. destruct PR. destruct REL; eauto with itree.
Qed.

Hint Resolve eqitC_dist : paco.

Lemma eqit_clo_trans b1 b2 vclo
      (MON: monotone2 vclo)
      (CMP: compose (eqitC b1 b2) vclo <3= compose vclo (eqitC b1 b2)):
  eqit_trans_clo b1 b2 false false <3= gupaco2 (eqit_ RR b1 b2 vclo) (eqitC b1 b2).
Proof.
  intros. destruct PR. gclo. econstructor; eauto with paco.
Qed.

Lemma eqtr_refl : forall (tr : trace A B), eqtr tr tr.
Proof.
red; intros.
ginit.
red.
pcofix CIH. gstep; intros.
intros; red.
destruct tr.

Lemma bisim_sym : forall tr1 tr2, bisim tr1 tr2 -> bisim tr2 tr1.
Proof.
