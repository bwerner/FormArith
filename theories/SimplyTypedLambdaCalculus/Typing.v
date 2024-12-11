(**
  This file defines the necessary to type the terms defined in [Terms.v].
  In particular, here are defined the [type]s and the [typing] judgements.
*)

From FormArith Require Export Base.
From FormArith.SimplyTypedLambdaCalculus Require Import Term.

(** * Typing *)

(** ** Definitions *)

(** *** Types of the simply-typed λ-calculus.

  Here, the classical types are extended with the product and sum types.
*)
Inductive type :=
  (** Base type *)
  | Base
  
  (** Arrow type: [A → B] *)
  | Arr (A B: type)

  (** Prod type: [A × B] *)
  | Prod (A B: type)

  (** Sum type: [A + B] *)
  | Sum (A B: type).

(** Notation of a typing judgement. *)
Reserved Notation "Γ ⊢ t : A" (at level 60, t at next level).

(** *** Typing rules of simply-typed λ-calculus *)
Inductive typing (Γ: var -> type): term -> type -> Prop :=
  (** **** Classical λ-calculus *)
  
  (** Γ(x) = A ⇒ Γ ⊢ x : A *)
  | Typing_Var (x: var) (A: type):
      Γ x = A -> Γ ⊢ Var x : A

  (** (Γ ⊢ s : A → B) ∧ (Γ ⊢ t : A) ⇒ Γ ⊢ s t : B *)
  | Typing_App (s t: term) (A B: type) :
      Γ ⊢ s : Arr A B ->
      Γ ⊢ t : A ->
      Γ ⊢ App s t : B

  (** Γ, A ⊢ s: B ⇒ Γ ⊢ λ s : A → B*)
  | Typing_Lam (s: term) (A B: type):
      A .: Γ ⊢ s : B ->
      Γ ⊢ Lam s : Arr A B

  (** **** Pairs and projections *)

  (** Γ ⊢ s : (A × B) ⇒ Γ ⊢ π1(s) : A *)
  | Typing_ProjL (s: term) (A B: type):
      Γ ⊢ s : Prod A B ->
      Γ ⊢ ProjL s : A

  (** Γ ⊢ s : (A × B) ⇒ Γ ⊢ π2(s) : A *)
  | Typing_ProjR (s: term) (A B: type):
      Γ ⊢ s : Prod A B ->
      Γ ⊢ ProjR s : B

  (** (Γ ⊢ s : A) ∧ (Γ ⊢ t : B) ⇒ Γ ⊢ (s, t) : (A × B) *)
  | Typing_Pair (s t: term) (A B: type):
      Γ ⊢ s : A ->
      Γ ⊢ t : B ->
      Γ ⊢ Pair s t : Prod A B

  (** **** Pattern matching and injections *)

  (** Γ ⊢ s : A ⇒ Γ ⊢ i(s) : A + B *)
  | Typing_InjL (s: term) (A B: type):
      Γ ⊢ s : A ->
      Γ ⊢ InjL s : Sum A B

  (** Γ ⊢ s : B ⇒ Γ ⊢ j(s) : A + B *)
  | Typing_InjR (s: term) (A B: type):
      Γ ⊢ s : B ->
      Γ ⊢ InjR s : Sum A B

  (** (Γ ⊢ t : A + B) ∧ (Γ, A ⊢ u : C) ∧ (Γ, B ⊢ v : C) ⇒ Γ ⊢ δ(t, u, v) : C *)
  | Typing_Sum (t u v: term) (A B C: type):
      Γ ⊢ t : Sum A B ->
      (A .: Γ) ⊢ u : C ->
      (B .: Γ) ⊢ v : C ->
      Γ ⊢ Case t u v : C
  where "Γ ⊢ t : A" := (typing Γ t A).


(** ** Properties *)

(** Weakening of a typing judgement. *)
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
    ? ? ? ? ? _ IH1 _ IH2 |
    ? ? A B _ IH |
    ? ? A B _ IH  |
    ? ? ? ? A B C _ IH1 _ IH2 _ IH3
  ]; intros ? ? HΓ; simpl.

  (* Classical λ-calculus *)
  - apply Typing_Var.
    now rewrite HΓ in H.

  - apply Typing_App with A.
    + now apply IH1.
    + now apply IH2.

  - apply Typing_Lam; asimpl.
    apply IH.
    now rewrite HΓ; asimpl.

  (* Product types *)
  - apply Typing_ProjL with B.
    now apply IH.

  - apply Typing_ProjR with A.
    now apply IH.

  - apply Typing_Pair.
    + now apply IH1.
    + now apply IH2.

  (* Case types *)
  - apply Typing_InjL.
    now apply IH.

  - apply Typing_InjR.
    now apply IH.

  - apply Typing_Sum with A B; asimpl.
    + now apply IH1.
    + apply IH2.
      now rewrite HΓ; asimpl.
    + apply IH3.
      now rewrite HΓ; asimpl.
Qed.

(** Γ ⊢ s : A ⇒ Γ' ⊢ s[σ] : A, where Γ' ⊢ σ(x) : Γ(x) for every variable x *)
Lemma type_subst (Γ Γ': var -> type) (s: term) (A: type) (σ: var -> term):
  Γ ⊢ s : A ->
  (forall (x: var), Γ' ⊢ σ x : Γ x) ->
  Γ' ⊢ s.[σ] : A.
Proof.
  revert Γ Γ' A σ.

  induction s as [
    | ? IH1 ? IH2 | ? IH
    | ? IH1 ? IH2 | ? IH | ? IH
    | ? IH1 ? IH2 ? IH3 | ? IH | ? IH
  ];
  intros Γ Γ' ? ? HΓ HΓ'; simpl.

  all: inv HΓ as [ | ? ? A' | ? A' | | | | | | ].

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

  - apply Typing_ProjL with B.
    now apply IH with Γ.

  - apply Typing_ProjR with A0.
    now apply IH with Γ.

  - apply Typing_Sum with (A := A0) (B := B).
    + now apply IH1 with Γ.
    + apply IH2 with (A0 .: Γ); [ assumption |].
      intros [| x ]; asimpl.
      * now apply Typing_Var.
      * now apply type_weakening with Γ'.
    + apply IH3 with (B .: Γ); [ assumption |].
      intros [| x ]; asimpl.
      * now apply Typing_Var.
      * now apply type_weakening with Γ'.

  - apply Typing_InjL.
    now apply IH with Γ.

  - apply Typing_InjR.
    now apply IH with Γ.
Qed.

(** Type preservation, i.e subject reduction *)
Lemma type_preservation (Γ: var -> type) (s t: term) (A: type):
  Γ ⊢ s : A -> s ~> t -> Γ ⊢ t : A.
Proof.
  revert Γ t A.

  induction s as [
    | ? IH1 ? IH2 | ? IH
    | ? IH1 ? IH2 | ? IH | ? IH
    | ? IH1 ? IH2 ? IH3 | ? IH | ? IH
  ]; intros Γ ? ? HΓ HΓ'; asimpl.

  all: inv HΓ.
  all: inv HΓ'.
  
  all: match goal with
       | H: _ ⊢ _ : Arr ?A _ |- _ => rename A into A'
       | H: _ ⊢ _ : Prod ?A _ |- _ => rename A into A'
       | H: _ ⊢ _ : Case ?A _ |- _ => rename A into A'
       | _ => idtac
       end.

  - match goal with
    | H: Γ ⊢ Lam s : _ |- _ => inv H
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

  - apply Typing_ProjL with B.
    now apply IH.

  - now inv H0.

  - apply Typing_ProjR with A'.
    now apply IH.

  - now inv H0.

  - apply Typing_Sum with A0 B.
    2, 3: assumption.
    now apply IH1.

  - apply Typing_Sum with A0 B.
    1, 3: assumption.
    now apply IH2.

  - apply Typing_Sum with A0 B.
    1, 2: assumption.
    now apply IH3.

  - apply type_subst with (A0 .: Γ); [ assumption |].
    intros [| x ]; asimpl.
    + now inv H2.
    + now apply Typing_Var.

  - apply type_subst with (B .: Γ); [ assumption |].
    intros [| x ]; asimpl.
    + now inv H2.
    + now apply Typing_Var.

  - apply Typing_InjL.
    now apply IH.

  - apply Typing_InjR.
    now apply IH.
Qed.
