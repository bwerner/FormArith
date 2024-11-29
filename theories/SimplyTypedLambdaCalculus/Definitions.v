From FormArith Require Export Base.

From Autosubst Require Export Autosubst.
Require Export Relations.Relations.

(** ### Useful Tactics ### *)
Ltac inv H := inversion H; subst; clear H.

(** ### Terms and Autosubst stuff ### *)
Inductive term : Type :=
  | Var (n: var)

  (** Basic lambda calculus *)
  | App (s t: term)
  | Lam (s: {bind term})

  (** Pairs and projections *)
  | Pair (s t: term)
  | Pr1 (s: term)
  | Pr2 (s: term)

  (** Injections and pattern matching *)
  | Pat (t: term) (u: {bind term}) (v: {bind term})
  | In1 (s: term)
  | In2 (s: term).

Instance Ids_term: Ids term. derive. Defined.
Instance Rename_term: Rename term. derive. Defined.
Instance Subst_term: Subst term. derive. Defined.
Instance SubstLemmas_term: SubstLemmas term. derive. Defined.

(** ### Beta reduction & reflexive transitive closure *)

Reserved Notation "t ~> t'" (at level 60).

Inductive beta: term -> term -> Prop :=
  (** Classical beta reduction *)
  | Beta_Subst (s s' t: term): s' = s.[t .: ids] -> (App (Lam s) t) ~> s'
  | Beta_AppL (s s' t: term): s ~> s' -> App s t ~> App s' t
  | Beta_AppR (s t t': term): t ~> t' -> App s t ~> App s t'
  | Beta_Lam (s s': term): s ~> s' -> Lam s ~> Lam s'

  (** Pairs and projectoins *)
  | Beta_Pair1 (s s' t: term): s ~> s' -> Pair s t ~> Pair s' t
  | Beta_Pair2 (s t t': term): t ~> t' -> Pair s t ~> Pair s t'
  | Beta_Pr1 (s s': term): s ~> s' -> Pr1 s ~> Pr1 s'
  | Beta_Pr2 (s s': term): s ~> s' -> Pr2 s ~> Pr2 s'
  | Beta_Pr1_Pair (s t: term): Pr1 (Pair s t) ~> s
  | Beta_Pr2_Pair (s t: term): Pr2 (Pair s t) ~> t

  (** Injections and pattern matching *)
  | Beta_Pat1 (t t' u v: term): t ~> t' -> Pat t u v ~> Pat t' u v
  | Beta_Pat2 (t u u' v: term): u ~> u' -> Pat t u v ~> Pat t u' v
  | Beta_Pat3 (t u v v': term): v ~> v' -> Pat t u v ~> Pat t u v'
  | Beta_In1 (s s': term): s ~> s' -> In1 s ~> In1 s'
  | Beta_In2 (s s': term): s ~> s' -> In2 s ~> In2 s'
  | Beta_Pat_In1 (t u u' v: term): u' = u.[t .: ids] -> Pat (In1 t) u v ~> u'
  | Beta_Pat_In2 (t u v v': term): v' = v.[t .: ids] -> Pat (In2 t) u v ~> v'

  where "t ~> t'" := (beta t t').

Notation "R *" := (clos_refl_trans _ R)
  (at level 8, no associativity, format "R *").
Notation "t ~>* t'" := (beta* t t') (at level 70, t' at next level).
Definition beta_rtcn1 := clos_refl_trans_1n _ beta.

Lemma beta_star_refl (t: term):
  t ~>* t.
Proof.
  apply rt_refl.
Qed.

Lemma beta_star_trans (x y z: term):
  x ~>* y -> y ~>* z -> x ~>* z.
Proof.
  intros Hxy Hyz.
  apply rt_trans with (y := y); assumption.
Qed.

Lemma beta_star_f1 (f: term -> term) (s s': term):
  (forall (s s': term), s ~> s' -> f s ~> f s') ->
  s ~>* s' -> f s ~>* f s'.
Proof.
  intros Hf Hs. induction Hs.
  - apply rt_step. apply Hf. assumption.
  - apply rt_refl.
  - apply rt_trans with (f y); assumption.
Qed.

Lemma beta_star_lam (s s': term):
  s ~>* s' ->
  Lam s ~>* Lam s'.
Proof.
  apply beta_star_f1. apply Beta_Lam.
Qed.

Lemma beta_star_f2 (f: term -> term -> term) (s s' t t': term):
  (forall (s s' t: term), s ~> s' -> f s t ~> f s' t) ->
  (forall (s t t': term), t ~> t' -> f s t ~> f s t') ->
  s ~>* s' -> t ~>* t' -> f s t ~>* f s' t'.
Proof.
  intros Hf1 Hf2 Hs Ht. apply rt_trans with (f s' t); [
      induction Hs |
      induction Ht
    ].
  2, 5: apply rt_refl.
  2, 4: eapply rt_trans; try eassumption.
  all: apply rt_step.
  1: apply Hf1.
  2: apply Hf2.
  all: assumption.
Qed.

Lemma beta_star_app (s s' t t': term):
  s ~>* s' ->
  t ~>* t' ->
  App s t ~>* App s' t'.
Proof.
  apply beta_star_f2.
  - apply Beta_AppL.
  - apply Beta_AppR.
Qed.

Lemma beta_star_f3 (f: term -> term -> term -> term) (s s' t t' u u': term):
  (forall (s s' t u: term), s ~> s' -> f s t u ~> f s' t u) ->
  (forall (s t t' u: term), t ~> t' -> f s t u ~> f s t' u) ->
  (forall (s t u u': term), u ~> u' -> f s t u ~> f s t u') ->
  s ~>* s' -> t ~>* t' -> u ~>* u' -> f s t u ~>* f s' t' u'.
Proof.
  intros Hf1 Hf2  Hf3 Hs Ht Hu. apply rt_trans with (f s' t u); [
      induction Hs |
      apply rt_trans with (f s' t' u)
    ].
  4: induction Ht.
  7: induction Hu.
  2, 5, 8: apply rt_refl.
  1, 3, 5: apply rt_step.
  1: apply Hf1. 2: apply Hf2. 3: apply Hf3.
  1, 2, 3: assumption.
  all : eapply rt_trans; eassumption.
Qed.

Lemma beta_star_pat (s s' t t' u u': term):
  s ~>* s' ->
  t ~>* t' ->
  u ~>* u' ->
  Pat s t u ~>* Pat s' t' u'.
Proof.
  apply beta_star_f3.
  - apply Beta_Pat1.
  - apply Beta_Pat2.
  - apply Beta_Pat3.
Qed.

Lemma beta_subst (t t': term) (σ: var -> term):
  t ~> t' -> t.[σ] ~> t'.[σ].
Proof.
  revert t' σ.

  induction t as [
    | ? IHs ? IHt | s IHs
    | s IHs t IHt | s IHs | s IHs
    | t IHt u IHu v IHv | s IHs | s IHs ].

  (** Classical lambda calculus *)
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

  (** Pairs and projections *)
  - intros t' σ Hbeta. inv Hbeta.
    + apply Beta_Pair1. apply IHs. assumption.
    + apply Beta_Pair2. apply IHt. assumption.

  - intros t' σ Hbeta. inv Hbeta.
    + apply Beta_Pr1. apply IHs. assumption.
    + apply Beta_Pr1_Pair.

  - intros t' σ Hbeta. inv Hbeta.
    + apply Beta_Pr2. apply IHs. assumption.
    + apply Beta_Pr2_Pair.

  (** Pattern matching and injections *)
  - intros t' σ Hbeta. inv Hbeta.
    + apply Beta_Pat1. now apply IHt.
    + apply Beta_Pat2. now apply IHu.
    + apply Beta_Pat3. now apply IHv.
    + apply Beta_Pat_In1. asimpl. reflexivity.
    + apply Beta_Pat_In2. asimpl. reflexivity.

  - intros t' σ Hbeta. inv Hbeta.
    apply Beta_In1. now apply IHs.

  - intros t' σ Hbeta. inv Hbeta.
    apply Beta_In2. now apply IHs.
Qed.

Inductive type :=
  | Base
  | Arr (A B: type)
  | Prod (A B: type)
  | Sum (A B: type).

Reserved Notation "Γ ⊢ t : A" (at level 60, t at next level).

Inductive typing (Γ: var -> type): term -> type -> Prop :=
  (** Classical Lambda Calculus *)
  | Typing_Var (x: var) (A: type):
      Γ x = A -> Γ ⊢ Var x : A

  | Typing_App (s t: term) (A B: type) :
      Γ ⊢ s : Arr A B ->
      Γ ⊢ t : A ->
      Γ ⊢ App s t : B

  | Typing_Lam (s: term) (A B: type):
      A .: Γ ⊢ s : B ->
      Γ ⊢ Lam s : Arr A B

  (** Pairs and projections *)
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

  (** Pattern matching and injections *)
  | Typing_In1 (s: term) (A B: type):
      Γ ⊢ s : A ->
      Γ ⊢ In1 s : Sum A B

  | Typing_In2 (s: term) (A B: type):
      Γ ⊢ s : B ->
      Γ ⊢ In2 s : Sum A B

  | Typing_Pat (t u v: term) (A B C: type):
      Γ ⊢ t : Sum A B ->
      (A .: Γ) ⊢ u : C ->
      (B .: Γ) ⊢ v : C ->
      Γ ⊢ Pat t u v : C

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
      ? ? ? ? ? _ IH1 _ IH2 |
      ? ? A B _ IH |
      ? ? A B _ IH  |
      ? ? ? ? A B C _ IH1 _ IH2 _ IH3
    ]; intros ? ? H'; simpl.

  (** Classical lambda calculus *)
  - apply Typing_Var.
    rewrite H' in H; simpl in H.
    assumption.

  - apply Typing_App with A.
    + now apply IH1.
    + now apply IH2.

  - apply Typing_Lam; asimpl.
    apply IH.
    now rewrite H'; asimpl.

  (** Product types *)
  - apply Typing_Pr1 with B.
    apply IH. assumption.

  - apply Typing_Pr2 with A.
    apply IH. assumption.

  - apply Typing_Pair.
    + now apply IH1.
    + now apply IH2.

  (** Sum types *)
  - apply Typing_In1. now apply IH.

  - apply Typing_In2. now apply IH.

  - apply Typing_Pat with (A := A) (B := B).
    + now apply IH1.
    + asimpl. apply IH2.
      now rewrite H'; asimpl.
    + asimpl. apply IH3.
      now rewrite H'; asimpl.
Qed.

Lemma type_subst (Γ Γ': var -> type) (s: term) (A: type) (σ: var -> term):
  Γ ⊢ s : A ->
  (forall (x: var) , Γ' ⊢ σ x : Γ x) ->
  Γ' ⊢ s.[σ] : A.
Proof.
  revert Γ Γ' A σ.

  induction s as [
    | ? IH1 ? IH2 | ? IH
    | ? IH1 ? IH2 | ? IH | ? IH
    | ? IH1 ? IH2 ? IH3 | ? IH | ? IH
    ];
  intros Γ Γ' ? ? HΓ HΓ'; simpl.
  all: inversion HΓ as [ | ? ? A' | ? A' |  |  | | | | ]; subst.

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

  - apply Typing_Pat with (A := A0) (B := B).
    + now apply IH1 with Γ.
    + apply IH2 with (A0 .: Γ); [ assumption |].
      intros [| x ]; asimpl.
      * now apply Typing_Var.
      * now apply type_weakening with Γ'.
    + apply IH3 with (B .: Γ); [ assumption |].
      intros [| x ]; asimpl.
      * now apply Typing_Var.
      * now apply type_weakening with Γ'.
  - apply Typing_In1. now apply IH with Γ.
  - apply Typing_In2. now apply IH with Γ.
Qed.

Lemma type_preservation (Γ: var -> type) (s t: term) (A: type):
  Γ ⊢ s : A -> s ~> t -> Γ ⊢ t : A.
Proof.
  revert Γ t A.

  induction s as [
    | ? IH1 ? IH2 | ? IH
    | ? IH1 ? IH2 | ? IH | ? IH
    | ? IH1 ? IH2 ? IH3 | ? IH | ? IH ]; intros Γ ? ? HΓ HΓ'; asimpl.
  all: inversion HΓ; subst.
  all: inversion HΓ' as [ s' | | | | | | | | | | | | | | | | ]; subst.
  
  all: match goal with
       | H: _ ⊢ _ : Arr ?A _ |- _ => rename A into A'
       | H: _ ⊢ _ : Prod ?A _ |- _ => rename A into A'
       | H: _ ⊢ _ : Sum ?A _ |- _ => rename A into A'
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

  - apply Typing_Pat with A' B.
    2, 3: assumption.
    now apply IH1.

  - apply Typing_Pat with A' B.
    1, 3: assumption.
    now apply IH2.

  - apply Typing_Pat with A' B.
    1, 2: assumption.
    now apply IH3.

  - apply type_subst with (A' .: Γ); [ assumption |].
    intros [| x ]; asimpl.
    + now inv H2.
    + now apply Typing_Var.

  - apply type_subst with (B .: Γ); [ assumption |].
    intros [| x ]; asimpl.
    + now inv H2.
    + now apply Typing_Var.

  - apply Typing_In1. now apply IH.

  - apply Typing_In2. now apply IH.
Qed.
