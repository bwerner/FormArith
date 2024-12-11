(**
  This project contains formalisation in Rocq of the 2.7.1 MPRI course:
  Foundations of proof systems.
*)

Require Export Nat.
Require Export Relations.Relations.

(** Force all the proof to have only one goal at a time. *)
#[export] Set Default Goal Selector "!".

(** The star defines the reflexive and transitive closure of a relation. *)
Notation "R *" := (clos_refl_trans _ R)
  (at level 8, no associativity, format "R *").

Tactic Notation "inv" hyp(H) :=
  inversion H; subst; clear H.

Tactic Notation "inv" hyp(H) "as" simple_intropattern(pat) :=
  let H' := fresh "H'" in
  rename H into H';
  inversion H' as pat; subst; clear H'.
