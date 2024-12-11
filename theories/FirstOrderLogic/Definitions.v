(**
  This section defines the first-order logic with some properties on derivations.

  This file contains terms, formulas, and an evaluation of formulas into Rocq [Prop].
*)

From FormArith Require Export Base.

Require Export List.

Unset Elimination Schemes.

(** * Terms *)

(** ** Terms of the first-order logic.

  They are defined as either a variable or a function applied to a list of
  terms.
*)
Inductive term :=
  (** A variable is defined by a natural number. *)
  | TVar : nat -> term

  (**
    A function is defined by a natural number and is applied to a list of terms
    defined inductively.
  *)
  | TApp : nat -> list term -> term.

(**
  As Rocq cannot induce an induction principle with induction hypothesis for
  indirect terms, for example the ones in lists, here is a better induction
  principle that includes [Forall P terms] in the [TApp] case.
*)
Lemma term_ind (P: term -> Prop):
  (forall (idx: nat), P (TVar idx)) ->
  (forall (fct_idx: nat) (terms: list term),
     Forall P terms -> P (TApp fct_idx terms)) ->
  forall t, P t.
Proof.
  intros HVar HApp.
  fix HR 1.

  intros [ ? | ? terms ].
  - apply HVar.
  - apply HApp.
    induction terms; constructor.
    + apply HR.
    + assumption.
Qed.

Set Elimination Schemes.

(** * Formulas *)

(** ** Formulas of the first-order logic

  The [forall] and [exists] formulas are represented using the De Bruijn
  indices.
*)
Inductive formula :=
  (**
    An atomic formula of the first-order logic.

    This corresponds to a predicate which is defined the same way as a
    function: a predicate is defined by a natural number and is applied to a
    list of terms.
  *)
  | FAtom : nat -> list term -> formula

  (** A conjunction of two formulas. *)
  | FConj : formula -> formula -> formula

  (** A disjunction of two formulas. *)
  | FDisj : formula -> formula -> formula

  (** An implication between two formulas. *)
  | FImp : formula -> formula -> formula

  (** Bottom, which represents the [False] formula. *)
  | FBot : formula

  (** Top, which represents the [True] formula. *)
  | FTop : formula

  (** Represents a formula starting with [forall]. *)
  | FForAll : formula -> formula

  (** Represents a formula starting with [exists]. *)
  | FExists : formula -> formula.

(**
  Auxiliary function of [formula_eval] that evaluates a term [t] in the
  environment [σ] with the environment of functions [fcts].
*)
Fixpoint term_eval (fcts: nat -> list nat -> nat) (σ: list nat) (t: term): nat :=
  match t with
  | TVar idx => nth idx σ 0
  | TApp fct_idx terms => fcts fct_idx (map (term_eval fcts σ) terms)
  end.

(**
  Evaluates a formula into a Rocq [Prop].

  Here, [fcts] is the environment of functions that are used in [term]
  definition: a function is denoted by a natural number, and maps a list of
  [nat] into a [nat].

  With the same idea, [preds] is the environment of predicates that are the
  atomic formulas: a predicate is denoted by a natural number, and maps a list
  of terms to a Rocq [Prop].
*)
Fixpoint formula_eval
    (fcts: nat -> list nat -> nat) (preds : nat -> list nat -> Prop)
    (σ: list nat) (phi: formula): Prop :=
  match phi with
  | FAtom pred_idx terms => preds pred_idx (map (term_eval fcts σ) terms)

  | FConj phi phi' => (formula_eval fcts preds σ phi) /\ (formula_eval fcts preds σ phi')
  | FDisj phi phi' => (formula_eval fcts preds σ phi) \/ (formula_eval fcts preds σ phi')
  | FImp phi phi' => (formula_eval fcts preds σ phi) -> (formula_eval fcts preds σ phi')

  | FBot => False
  | FTop => True

  | FForAll phi => forall x, formula_eval fcts preds (x :: σ) phi
  | FExists phi => exists x, formula_eval fcts preds (x :: σ) phi
  end.
