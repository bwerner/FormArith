Require Export Nat.
Require Export Relations.Relations.

#[export] Set Default Goal Selector "!".

Notation "R *" := (clos_refl_trans _ R)
  (at level 8, no associativity, format "R *").

Tactic Notation "inv" hyp(H) :=
  inversion H; subst; clear H.

Tactic Notation "inv" hyp(H) "as" simple_intropattern(pat) :=
  let H' := fresh "H'" in
  rename H into H';
  inversion H' as pat; subst; clear H'.
