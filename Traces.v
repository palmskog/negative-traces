Set Primitive Projections.

Section Trace.

Variables A B : Type.

Inductive traceF (X : Type) : Type :=
| TnilF : A -> traceF X
| TconsF : A -> B -> X -> traceF X.

CoInductive trace := gotrace { untrace : traceF trace }.

End Trace.

Notation trace' A B := (traceF A B (trace A B)).

Definition observe {A B} (tr : trace A B) : trace' A B := @untrace A B tr.

Notation Tnil a := (gotrace _ _ (TnilF _ _ _ a)).
Notation Tcons a b tr := (gotrace _ _ (TconsF _ _ _ a b tr)).

Section Operations.

Variables A B : Type.

Definition hd (tr : trace A B) : A :=
match observe tr with
| TnilF _ _ _ a => a
| TconsF _ _ _ a b tr0 => a
end.

CoFixpoint trace_append (tr tr' : trace A B) : trace A B :=
match observe tr with
| TnilF _ _ _ _ => tr'
| TconsF _ _ _ a b tr0 => Tcons a b (trace_append tr' tr0)
end.

#[local] Infix "+++" := trace_append (at level 60, right associativity).

End Operations.

Section Eqtr.

Context {E : Type -> Type} {R1 R2 : Type} (RR : R1 -> R2 -> Prop).

End Eqtr.
