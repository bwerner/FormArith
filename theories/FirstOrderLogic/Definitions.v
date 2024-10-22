From FormArith Require Export Base.

Require Export List.

Unset Elimination Schemes.

Inductive term :=
  | TVar : nat -> term
  | TApp : nat -> list term -> term.

(* NOTE: Define induction principle to include `Forall P terms` for `TApp` *)
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

Inductive formula :=
  | FAtom : nat -> list term -> formula
  | FConj : formula -> formula -> formula
  | FDisj : formula -> formula -> formula
  | FImp : formula -> formula -> formula
  | FBot : formula
  | FTop : formula
  | FForAll : formula -> formula
  | FExists : formula -> formula.

Fixpoint term_eval (fcts: nat -> list nat -> nat) (sigma: list nat) (t: term): nat :=
  match t with
  | TVar idx => nth idx sigma 0
  | TApp fct_idx terms => fcts fct_idx (map (term_eval fcts sigma) terms)
  end.

Fixpoint formula_eval
    (fcts: nat -> list nat -> nat) (preds : nat -> list nat -> Prop)
    (sigma: list nat) (phi: formula): Prop :=
  match phi with
  | FAtom pred_idx terms => preds pred_idx (map (term_eval fcts sigma) terms)

  | FConj phi phi' => (formula_eval fcts preds sigma phi) /\ (formula_eval fcts preds sigma phi')
  | FDisj phi phi' => (formula_eval fcts preds sigma phi) \/ (formula_eval fcts preds sigma phi')
  | FImp phi phi' => (formula_eval fcts preds sigma phi) -> (formula_eval fcts preds sigma phi')

  | FBot => False
  | FTop => True

  | FForAll phi => forall x, formula_eval fcts preds (x :: sigma) phi
  | FExists phi => exists x, formula_eval fcts preds (x :: sigma) phi
  end.


Lemma app_cons_nil {T: Type} (l l': list T) (x: T):
  (l ++ x :: nil) ++ l' = l ++ x :: l'.
Proof.
  induction l as [| ? ? IHl ]; simpl.
  { reflexivity. }

  rewrite IHl.
  reflexivity.
Qed.
