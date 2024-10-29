From FormArith Require Export Base.

From Autosubst Require Export Autosubst.

Inductive term : Type :=
  | Var (n: var)
  | App (s t: term)
  | Lam (s: {bind term}).

Instance Ids_term: Ids term. derive. Defined.
Instance Rename_term: Rename term. derive. Defined.
Instance Subst_term: Subst term. derive. Defined.
Instance SubstLemmas_term: SubstLemmas term. derive. Defined.


Inductive step: term -> term -> Prop :=
  | Step_beta (s s' t: term): s' = s.[t .: ids] -> step (App (Lam s) t) s'
  | Step_app1 (s s' t: term): step s s' -> step (App s t) (App s' t)
  | Step_app2 (s t t': term): step t t' -> step (App s t) (App s t')
  | Step_lam (s s': term): step s s' -> step (Lam s) (Lam s').

Lemma step_subst (t t': term) (sigma: var -> term):
  step t t' -> step t.[sigma] t'.[sigma].
Proof.
  revert t' sigma.

  induction t as [ | ? IHs ? IHt | s IHs ].
  - inversion 1.

  - inversion 1; subst; simpl.
    + apply Step_beta.
      asimpl.
      reflexivity.

    + apply Step_app1.
      apply IHs.
      assumption.

    + apply Step_app2.
      apply IHt.
      assumption.

  - inversion 1; subst; simpl.
    apply Step_lam.
    apply IHs.
    assumption.
Qed.


Inductive type :=
  | Base
  | Arr (A B: type).

Inductive types (Gamma: var -> type): term -> type -> Prop :=
  | Types_var (x: var) (A: type):
      Gamma x = A -> types Gamma (Var x) A

  | Types_app (s t: term) (A B: type) :
      types Gamma s (Arr A B) ->
      types Gamma t A ->
      types Gamma (App s t) B

  | Types_lam (s: term) (A B: type):
      types (A .: Gamma) s B ->
      types Gamma (Lam s) (Arr A B).

Lemma type_weakening (gamma: var -> type) (s: term) (A: type):
  types gamma s A ->
    forall (gamma': var -> type) (x': var -> var),
      gamma = x' >>> gamma' -> types gamma' s.[ren x'] A.
Proof.
  induction 1 as [ ? ? ? H | ? ? ? A ? _ IH1 _ IH2 | ? ? ? ? _ IH ]; intros ? ? H'; simpl.
  - apply Types_var.
    rewrite H' in H; simpl in H.
    assumption.

  - apply Types_app with A.
    + now apply IH1.
    + now apply IH2.

  - apply Types_lam; asimpl.
    apply IH.
    now rewrite H'; asimpl.
Qed.

Lemma type_subst (gamma gamma': var -> type) (s: term) (A: type) (sigma: var -> term):
  types gamma s A ->
  (forall (x: var) , types gamma' (sigma x) (gamma x)) ->
  types gamma' s.[sigma] A.
Proof.
  revert gamma gamma' A sigma.

  induction s as [ | ? IH1 ? IH2 | ? IH ]; intros gamma gamma' ? ? Hgamma Hgamma'; simpl.
  all: inversion Hgamma as [ | ? ? A' | ? A' ]; subst.

  - apply Hgamma'.
  - apply Types_app with A'.
    + now apply IH1 with gamma.
    + now apply IH2 with gamma.
  - apply Types_lam.
    apply IH with (A' .: gamma); [ assumption |].
    intros [| x ]; asimpl.
    + now apply Types_var.
    + now apply type_weakening with gamma'.
Qed.

Lemma type_preservation (gamma: var -> type) (s t: term) (A: type):
  types gamma s A -> step s t -> types gamma t A.
Proof.
  revert gamma t A.

  induction s as [ | ? IH1 ? IH2 | ? IH ]; intros gamma ? ? Hgamma Hgamma'; asimpl.
  all: inversion Hgamma; subst.
  all: inversion Hgamma' as [ s' | | | ]; subst.

  all: match goal with
       | H: types _ _ (Arr ?A _) |- _ => rename A into A'
       end.

  - match goal with
    | H: types gamma (Lam s') _ |- _ => inversion H; subst
    end.

    apply type_subst with (A' .: gamma); [ assumption |].
    intros [| x ]; asimpl; [ assumption |].
    now apply Types_var.

  - apply Types_app with A'; [| assumption ].
    now apply IH1.

  - apply Types_app with A'; [ assumption |].
    now apply IH2.

  - apply Types_lam.
    now apply IH.
Qed.
