From FormArith Require Export Base.

From Autosubst Require Export Autosubst.

(** Useful Tactics *)

Ltac inv H := inversion H; subst; clear H.

Inductive term : Type :=
  | Var (n: var)

  (** Basic lambda calculus *)
  | App (s t: term)
  | Lam (s: {bind term})

  (** Pairs and projections *)
  | Pair (s t: term)
  | Pr1 (s: term)
  | Pr2 (s: term).

Instance Ids_term: Ids term. derive. Defined.
Instance Rename_term: Rename term. derive. Defined.
Instance Subst_term: Subst term. derive. Defined.
Instance SubstLemmas_term: SubstLemmas term. derive. Defined.


Reserved Notation "t ~> t'" (at level 60).

Inductive beta: term -> term -> Prop :=
  | Beta_Subst (s s' t: term): s' = s.[t .: ids] -> (App (Lam s) t) ~> s'
  | Beta_AppL (s s' t: term): s ~> s' -> App s t ~> App s' t
  | Beta_AppR (s t t': term): t ~> t' -> App s t ~> App s t'
  | Beta_Lam (s s': term): s ~> s' -> Lam s ~> Lam s'
  | Beta_Pair1 (s s' t: term): s ~> s' -> Pair s t ~> Pair s' t
  | Beta_Pair2 (s t t': term): t ~> t' -> Pair s t ~> Pair s t'
  | Beta_Pr1 (s s': term): s ~> s' -> Pr1 s ~> Pr1 s'
  | Beta_Pr2 (s s': term): s ~> s' -> Pr2 s ~> Pr2 s'
  | Beta_Pr1_Pair (s t: term): Pr1 (Pair s t) ~> s
  | Beta_Pr2_Pair (s t: term): Pr2 (Pair s t) ~> t
  where "t ~> t'" := (beta t t').


Lemma beta_subst (t t': term) (σ: var -> term):
  t ~> t' -> t.[σ] ~> t'.[σ].
Proof.
  revert t' σ.

  induction t as [ | ? IHs ? IHt | s IHs | s IHs t IHt | s IHs | s IHs ].
  - inversion 1.

  - inversion 1; subst; simpl.
    + apply Beta_Subst.
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

  - intros t' σ Hbeta. inv Hbeta.
    + simpl. apply Beta_Pair1. apply IHs. assumption.
    + simpl. apply Beta_Pair2. apply IHt. assumption.

  - intros t' σ Hbeta. inv Hbeta.
    + simpl. apply Beta_Pr1. apply IHs. assumption.
    + simpl. apply Beta_Pr1_Pair.

  - intros t' σ Hbeta. inv Hbeta.
    + simpl. apply Beta_Pr2. apply IHs. assumption.
    + simpl. apply Beta_Pr2_Pair.
Qed.


Inductive type :=
  | Base
  | Arr (A B: type)
  | Prod (A B: type).

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

  | Typing_Pr1 (s: term) (A B: type):
      Γ ⊢ s : Prod A B ->
      Γ ⊢ Pr1 s : A

  | Typing_Pr2 (s: term) (A B: type):
      Γ ⊢ s : Prod A B ->
      Γ ⊢ Pr2 s : B

  | Typing_Pair (s t: term) (A B: type):
      Γ ⊢ s : A ->
      Γ ⊢ t : B ->
      Γ ⊢ Pair s t : Prod A B

  where "Γ ⊢ t : A" := (typing Γ t A).

Lemma type_weakening (Γ: var -> type) (s: term) (A: type):
  Γ ⊢ s : A ->
    forall (Γ': var -> type) (x': var -> var),
      Γ = x' >>> Γ' -> Γ' ⊢ s.[ren x'] : A.
Proof.
  induction 1 as [
      ? ? ? H |
      ? ? ? A ? _ IH1 _ IH2 |
      ? ? A B _ IH |
      ? ? A B _ IH |
      ? ? ? ? _ IH |
      ? ? ? ? ? _ IH1 _ IH2
    ]; intros ? ? H'; simpl.
  - apply Typing_Var.
    rewrite H' in H; simpl in H.
    assumption.

  - apply Typing_App with A.
    + now apply IH1.
    + now apply IH2.

  - apply Typing_Lam; asimpl.
    apply IH.
    now rewrite H'; asimpl.

  - apply Typing_Pr1 with B.
    apply IH. assumption.

  - apply Typing_Pr2 with A.
    apply IH. assumption.

  - apply Typing_Pair.
    + now apply IH1.
    + now apply IH2.
Qed.

Lemma type_subst (Γ Γ': var -> type) (s: term) (A: type) (σ: var -> term):
  Γ ⊢ s : A ->
  (forall (x: var) , Γ' ⊢ σ x : Γ x) ->
  Γ' ⊢ s.[σ] : A.
Proof.
  revert Γ Γ' A σ.

  induction s as [ | ? IH1 ? IH2 | ? IH | ? IH1 ? IH2 | ? IH | ? IH ]; intros Γ Γ' ? ? HΓ HΓ'; simpl.
  all: inversion HΓ as [ | ? ? A' | ? A' |  |  | ]; subst.

  - apply HΓ'.
  - apply Typing_App with A'.
    + now apply IH1 with Γ.
    + now apply IH2 with Γ.
  - apply Typing_Lam.
    apply IH with (A' .: Γ); [ assumption |].
    intros [| x ]; asimpl.
    + now apply Typing_Var.
    + now apply type_weakening with Γ'.
  - apply Typing_Pair.
    + now apply IH1 with Γ.
    + now apply IH2 with Γ.
  - apply Typing_Pr1 with B.
    now apply IH with Γ.
  - eapply Typing_Pr2. eapply IH with Γ; eassumption.
Qed.

Lemma type_preservation (Γ: var -> type) (s t: term) (A: type):
  Γ ⊢ s : A -> s ~> t -> Γ ⊢ t : A.
Proof.
  revert Γ t A.

  induction s as [ | ? IH1 ? IH2 | ? IH | ? IH1 ? IH2 | ? IH | ? IH ]; intros Γ ? ? HΓ HΓ'; asimpl.
  all: inversion HΓ; subst.
  all: inversion HΓ' as [ s' | | | | | | | | | ]; subst.

  all: match goal with
       | H: _ ⊢ _ : Arr ?A _ |- _ => rename A into A'
       | _ => idtac
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

  - apply Typing_Pair.
    + now apply IH1.
    + assumption.

  - apply Typing_Pair.
    + assumption.
    + now apply IH2.

  - apply Typing_Pr1 with B.
    now apply IH.

  - now inv H0.

  - eapply Typing_Pr2. eapply IH; eassumption.

  - now inv H0.
Qed.
