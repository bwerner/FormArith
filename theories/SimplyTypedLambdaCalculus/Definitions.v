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


Reserved Notation "t ->β t'" (at level 60).

Inductive beta: term -> term -> Prop :=
  | Beta_subst (s s' t: term): s' = s.[t .: ids] -> (App (Lam s) t) ->β s'
  | Beta_AppL (s s' t: term): s ->β s' -> App s t ->β App s' t
  | Beta_AppR (s t t': term): t ->β t' -> App s t ->β App s t'
  | Beta_Lam (s s': term): s ->β s' -> Lam s ->β Lam s'
  where "t ->β t'" := (beta t t').


Lemma beta_subst (t t': term) (σ: var -> term):
  t ->β t' -> t.[σ] ->β t'.[σ].
Proof.
  revert t' σ.

  induction t as [ | ? IHs ? IHt | s IHs ].
  - inversion 1.

  - inversion 1; subst; simpl.
    + apply Beta_subst.
      asimpl.
      reflexivity.

    + apply Beta_AppL.
      apply IHs.
      assumption.

    + apply Beta_AppR.
      apply IHt.
      assumption.

  - inversion 1; subst; simpl.
    apply Beta_Lam.
    apply IHs.
    assumption.
Qed.


Inductive type :=
  | Base
  | Arr (A B: type).

Reserved Notation "Γ ⊢ t : A" (at level 60, t at next level).

Inductive typing (Γ: var -> type): term -> type -> Prop :=
  | Typing_Var (x: var) (A: type):
      Γ x = A -> Γ ⊢ Var x : A

  | Typing_App (s t: term) (A B: type) :
      Γ ⊢ s : Arr A B ->
      Γ ⊢ t : A ->
      Γ ⊢ App s t : B

  | Typing_Lam (s: term) (A B: type):
      A .: Γ ⊢ s : B ->
      Γ ⊢ Lam s : Arr A B
  where "Γ ⊢ t : A" := (typing Γ t A).

Lemma type_weakening (Γ: var -> type) (s: term) (A: type):
  Γ ⊢ s : A ->
    forall (Γ': var -> type) (x': var -> var),
      Γ = x' >>> Γ' -> Γ' ⊢ s.[ren x'] : A.
Proof.
  induction 1 as [ ? ? ? H | ? ? ? A ? _ IH1 _ IH2 | ? ? ? ? _ IH ]; intros ? ? H'; simpl.
  - apply Typing_Var.
    rewrite H' in H; simpl in H.
    assumption.

  - apply Typing_App with A.
    + now apply IH1.
    + now apply IH2.

  - apply Typing_Lam; asimpl.
    apply IH.
    now rewrite H'; asimpl.
Qed.

Lemma type_subst (Γ Γ': var -> type) (s: term) (A: type) (σ: var -> term):
  Γ ⊢ s : A ->
  (forall (x: var) , Γ' ⊢ σ x : Γ x) ->
  Γ' ⊢ s.[σ] : A.
Proof.
  revert Γ Γ' A σ.

  induction s as [ | ? IH1 ? IH2 | ? IH ]; intros Γ Γ' ? ? HΓ HΓ'; simpl.
  all: inversion HΓ as [ | ? ? A' | ? A' ]; subst.

  - apply HΓ'.
  - apply Typing_App with A'.
    + now apply IH1 with Γ.
    + now apply IH2 with Γ.
  - apply Typing_Lam.
    apply IH with (A' .: Γ); [ assumption |].
    intros [| x ]; asimpl.
    + now apply Typing_Var.
    + now apply type_weakening with Γ'.
Qed.

Lemma type_preservation (Γ: var -> type) (s t: term) (A: type):
  Γ ⊢ s : A -> s ->β t -> Γ ⊢ t : A.
Proof.
  revert Γ t A.

  induction s as [ | ? IH1 ? IH2 | ? IH ]; intros Γ ? ? HΓ HΓ'; asimpl.
  all: inversion HΓ; subst.
  all: inversion HΓ' as [ s' | | | ]; subst.

  all: match goal with
       | H: _ ⊢ _ : Arr ?A _ |- _ => rename A into A'
       end.

  - match goal with
    | H: Γ ⊢ Lam s' : _ |- _ => inversion H; subst
    end.

    apply type_subst with (A' .: Γ); [ assumption |].
    intros [| x ]; asimpl; [ assumption |].
    now apply Typing_Var.

  - apply Typing_App with A'; [| assumption ].
    now apply IH1.

  - apply Typing_App with A'; [ assumption |].
    now apply IH2.

  - apply Typing_Lam.
    now apply IH.
Qed.
