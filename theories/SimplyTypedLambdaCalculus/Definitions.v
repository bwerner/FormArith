From FormArith Require Export Base.

From Autosubst Require Export Autosubst.

Inductive term : Type :=
  | Var (n: var)
  | App (s t: term)
  | Lam (s: {bind term})
  | Const_0
  | Const_S (s: term)
  | Rec   (t0 tn n: term).

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
  | Beta_S (s s': term): s ~> s' -> Const_S s ~> Const_S s'
  | Beta_R0 (t0 tn : term): Rec t0 tn Const_0 ~> t0
  | Beta_RS (t0 tn n : term): Rec t0 tn (Const_S n) ~> (App (App tn n) (Rec t0 tn n))
  | Beta_RI0 (t0 t0' tn n : term): t0 ~> t0' -> Rec t0 tn n ~> Rec t0' tn n
  | Beta_RIS (t0 tn tn' n : term): tn ~> tn' -> Rec t0 tn n ~> Rec t0 tn' n
  where "t ~> t'" := (beta t t').


Lemma beta_subst (t t': term) (σ: var -> term):
  t ~> t' -> t.[σ] ~> t'.[σ].
Proof.
  revert t' σ.

  induction t as [ | ? IHs ? IHt | s IHs | | | ? IH1 ? IH2 ? ?].
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

  (* zero is a constant and does not reduce *)
  - inversion 1.

  (* case: S n *)
  - inversion 1; subst.
    apply Beta_S. apply IHt. assumption.
    

  (* case: R operator *)
  - inversion 1; subst; simpl.
    + apply Beta_R0.
    + apply Beta_RS.
    + apply Beta_RI0. apply IH1. assumption.
    + apply Beta_RIS. apply IH2. assumption.
    
Qed.


Inductive type :=
  | Base
  | Nat
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

  | Typing_0: Γ ⊢ Const_0 : Nat
  | Typing_S (n: term): Γ ⊢ n : Nat -> Γ ⊢ (Const_S n) : Nat

  | Typing_R (t0 ts n: term) (A: type):
      Γ ⊢ t0 : A
      -> Γ ⊢ ts : (Arr Nat (Arr A A))
      -> Γ ⊢ n : Nat
      -> Γ ⊢ Rec t0 ts n : A
  where "Γ ⊢ t : A" := (typing Γ t A).

Lemma type_weakening (Γ: var -> type) (s: term) (A: type):
  Γ ⊢ s : A ->
    forall (Γ': var -> type) (x': var -> var),
      Γ = x' >>> Γ' -> Γ' ⊢ s.[ren x'] : A.
Proof.
  induction 1 as [ ? ? ? H 
                 | ? ? ? A ? _ IH1 _ IH2
                 | ? ? ? ? _ IH
                 |
                 | ? ? ? IH
                 | ? ? ? ? ? ? IH1 ? IH2 ? IH3]; intros ? ? H'; simpl.
  - apply Typing_Var.
    rewrite H' in H; simpl in H.
    assumption.

  - apply Typing_App with A.
    + now apply IH1.
    + now apply IH2.

  - apply Typing_Lam; asimpl.
    apply IH.
    now rewrite H'; asimpl.

  - apply Typing_0.
  - apply Typing_S. apply IH. assumption.
  - apply Typing_R.
    + apply IH1. assumption.
    + apply IH2. assumption.
    + apply IH3. assumption.
Qed.

Lemma type_subst (Γ Γ': var -> type) (s: term) (A: type) (σ: var -> term):
  Γ ⊢ s : A ->
  (forall (x: var) , Γ' ⊢ σ x : Γ x) ->
  Γ' ⊢ s.[σ] : A.
Proof.
  revert Γ Γ' A σ.

  induction s as [ | ? IH1 ? IH2 | ? IH | | | ? IH1 ? IH2 ? IH3];
    intros Γ Γ' ? ? HΓ HΓ'; simpl.
  all: inversion HΓ as [ | ? ? A' | ? A' | | | ]; subst.

  - apply HΓ'.
  - apply Typing_App with A'.
    + now apply IH1 with Γ.
    + now apply IH2 with Γ.
  - apply Typing_Lam.
    apply IH with (A' .: Γ); [ assumption |].
    intros [| x ]; asimpl.
    + now apply Typing_Var.
    + now apply type_weakening with Γ'.
  - apply Typing_0.
  - apply Typing_S. apply IHs with (Γ := Γ). all: assumption.
  - apply Typing_R.
    + apply IH1 with (Γ := Γ). all: assumption.
    + apply IH2 with (Γ := Γ). all: assumption.
    + apply IH3 with (Γ := Γ). all: assumption.
Qed.

(* subject reduction *)
Lemma type_preservation (Γ: var -> type) (s t: term) (A: type):
  Γ ⊢ s : A -> s ~> t -> Γ ⊢ t : A.
Proof.
  revert Γ t A.

  induction s as [ | ? IH1 ? IH2 | ? IH | | | ]; intros Γ ? ? HΓ HΓ'; asimpl.
  all: inversion HΓ; subst.
  all: inversion HΓ'; subst.
  - inversion H1. subst.
    apply type_subst with (A0 .: Γ); [assumption |].
    intros [|x]; asimpl; [assumption |].
    now apply Typing_Var.
  - apply Typing_App with (A := A0); [| assumption].
    apply IH1. all: assumption.
  - apply Typing_App with (A := A0); [assumption |].
    apply IH2. all: assumption.
  - inversion HΓ'; subst. apply Typing_Lam. apply IH. all: assumption.

  - apply Typing_S. apply IHs. all: assumption. 

  - clear IHs3. assumption.

  - clear IHs3. inversion H5; subst.
    apply Typing_App with (A := A).
    + apply Typing_App with (A := Nat). all: assumption.
    + apply Typing_R. all: assumption.
  - apply Typing_R; [ | assumption .. ].
    apply IHs1. all: assumption.
  - apply Typing_R; [assumption | | assumption].
    apply IHs2. all: assumption.
Qed.
