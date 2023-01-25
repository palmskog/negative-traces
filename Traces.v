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

Definition eqtr_ sim :
  trace A B -> trace A B -> Prop :=
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

End Eqtr.
