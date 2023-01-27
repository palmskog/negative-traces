From Coq Require Import Arith Bool List.
From Giskard Require Import structures local.
From RecordUpdate Require Import RecordSet.

Import ListNotations.
Import RecordSetNotations.

Set Implicit Arguments.

(* BEGIN BOILERPLATE *)

#[export] Instance message_Settable : Settable _ :=
  settable! mkMessage <get_message_type;get_view;get_sender;get_block;get_piggyback_block>.

#[export] Instance NState_Settable : Settable _ :=
  settable! mkNState <node_view;node_id;in_messages;counting_messages;out_messages;timeout>.

(* END BOILERPLATE *)

(* BEGIN STATE FUNCTIONS *)

Definition record_set (s : NState) (m : message) : NState :=
 s <| out_messages := m :: s.(out_messages) |>.

Definition record_plural_set (s : NState) (lm : list message) : NState :=
 s <| out_messages := lm ++ s.(out_messages) |>.

Definition add_set (s : NState) (m : message) : NState :=
 s <| in_messages := m :: s.(in_messages) |>.

Definition add_plural_set (s : NState) (lm : list message) : NState :=
 s <| in_messages := lm ++ s.(in_messages) |>.

Definition discard_set (s : NState) (m : message) : NState :=
 s <| in_messages := remove message_eq_dec m s.(in_messages) |>.

Definition process_set (s : NState) (msg : message) : NState :=
 s <| in_messages := remove message_eq_dec msg (in_messages s) |>
   <| counting_messages := msg :: counting_messages s |>.

Definition increment_view_set (s : NState) : NState :=
 s <| node_view := S (node_view s) |>
   <| in_messages := [] |>
   <| timeout := false |>.

Definition propose_block_init_set (s : NState) (msg : message) :
 NState * list message :=
let lm := make_PrepareBlocks s (GenesisBlock_message s) in
(record_plural_set s lm, lm).

Definition process_timeout_set (s : NState) (msg : message) :
 NState * list message :=
let lm := [make_ViewChange s; highest_prepare_block_message s] in
(record_plural_set s lm,lm).

Definition discard_view_invalid_set (s : NState) (msg : message) :
 NState * list message :=
(discard s msg, []).

Definition process_PrepareBlock_duplicate (s : NState) (msg : message) (s' : NState) (lm : list message) : Prop :=
  s' = discard s msg /\
  lm = [] /\
  received s msg /\ 
  honest_node (node_id s) /\ 
  get_message_type msg = PrepareBlock /\ 
  view_valid s msg /\
  timeout s = false /\ 
  exists_same_height_PrepareBlock s (get_block msg).

(* END STATE FUNCTIONS *)

(* BEGIN REFINEMENT PROOFS *)

Lemma record_set_eq : forall s m,
 record s m = record_set s m.
Proof. reflexivity. Qed.

Lemma record_plural_set_eq : forall s lm,
 record_plural s lm = record_plural_set s lm.
Proof. reflexivity. Qed.

Lemma add_set_eq : forall s m,
 add s m = add_set s m.
Proof. reflexivity. Qed.

Lemma add_plural_set_eq : forall s lm,
 add_plural s lm = add_plural_set s lm.
Proof. reflexivity. Qed.

Lemma discard_set_eq : forall s m,
 discard s m = discard_set s m.
Proof. reflexivity. Qed.

Lemma process_set_eq : forall s msg,
 process s msg = process_set s msg.
Proof. reflexivity. Qed.

Lemma increment_view_set_eq : forall s,
 increment_view s = increment_view_set s.
Proof. reflexivity. Qed.

(* END REFINEMENT PROOFS *)
