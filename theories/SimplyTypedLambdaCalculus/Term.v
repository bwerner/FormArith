(**
  This file defines the basis of the simply-typed λ-calculus: in particular
  the terms, the β-reduction and some properties around them.
*)

From FormArith Require Export Base.

From Autosubst Require Export Autosubst.


(** * Terms of the simply-typed λ-calculus *)

(** ** Terms *)

(** *** Terms of the simply-typed λ-calculus.

  The library <<Autosubst>> is used to handle automatically the bounded
  variables in the λ-abstractions.
*)
Inductive term : Type :=
  (** **** Constructions of basic λ-calculus *)

  (**
    A simple variable.

    Its type [var] is defined in <<Autosubst>>.
  *)
  | Var (n: var)
  
  (** Application *)
  | App (s t: term)

  (** λ-abstraction *)
  | Lam (s: {bind term})

  (** **** Extension with pairs and projections *)

  (** Pair of two terms *)
  | Pair (s t: term)

  (** Left projection: π1 *)
  | ProjL (s: term)

  (** Right projection: π2 *)
  | ProjR (s: term)

  (** **** Extension with injections and pattern matching *)

  (** Pattern matching on a term: δ *)
  | Case (t: term) (u: {bind term}) (v: {bind term})

  (** Left injection: i *)
  | InjL (s: term)

  (** Right injection: j *)
  | InjR (s: term).

(* Autosubst required magic *)
Instance Ids_term: Ids term. derive. Defined.
Instance Rename_term: Rename term. derive. Defined.
Instance Subst_term: Subst term. derive. Defined.
Instance SubstLemmas_term: SubstLemmas term. derive. Defined.


(** ** β-reduction *)

(** Notation of the β-reduction *)
Reserved Notation "t ~> t'" (at level 60).

(** *** Rules of the β-reduction for the simply-typed λ-calculus. *)
Inductive beta: term -> term -> Prop :=
  (** **** Classical beta reduction *)

  (**
    Substitution rule.

    The actual substitution is handled though the <<Autosubst>> library.  
  *)
  | Beta_Subst (s s' t: term): s' = s.[t .: ids] -> (App (Lam s) t) ~> s'

  (** Reduction in the left part of an [App] *)
  | Beta_AppL (s s' t: term): s ~> s' -> App s t ~> App s' t

  (** Reduction in the right part of an [App] *)
  | Beta_AppR (s t t': term): t ~> t' -> App s t ~> App s t'

  (** Reduction under a [Lam] *)
  | Beta_Lam (s s': term): s ~> s' -> Lam s ~> Lam s'

  (** **** Pairs and projections *)

  (** Reduction in the left part of a [Pair] *)
  | Beta_Pair1 (s s' t: term): s ~> s' -> Pair s t ~> Pair s' t

  (** Reduction in the right part of a [Pair] *)
  | Beta_Pair2 (s t t': term): t ~> t' -> Pair s t ~> Pair s t'

  (** Reduction under a [ProjL] *)
  | Beta_ProjL (s s': term): s ~> s' -> ProjL s ~> ProjL s'

  (** Reduction under a [ProjR] *)
  | Beta_ProjR (s s': term): s ~> s' -> ProjR s ~> ProjR s'

  (** Reduction of a [Pair] in a left projection *)
  | Beta_ProjL_Pair (s t: term): ProjL (Pair s t) ~> s

  (** Reduction of a [Pair] in a right projection *)
  | Beta_ProjR_Pair (s t: term): ProjR (Pair s t) ~> t

  (** **** Injections and pattern matching *)
  
  (** Reduction in the matched part of a [Case] *)
  | Beta_Case1 (t t' u v: term): t ~> t' -> Case t u v ~> Case t' u v

  (** Reduction in the first case of a [Case] *)
  | Beta_Case2 (t u u' v: term): u ~> u' -> Case t u v ~> Case t u' v

  (** Reduction in the second case of a [Case] *)
  | Beta_Case3 (t u v v': term): v ~> v' -> Case t u v ~> Case t u v'

  (** Reduction under a [InjL] *)
  | Beta_InjL (s s': term): s ~> s' -> InjL s ~> InjL s'

  (** Reduction under a [InjR] *)
  | Beta_InjR (s s': term): s ~> s' -> InjR s ~> InjR s'

  (** Reduction of a [Case] with a left injection *)
  | Beta_Case_InjL (t u u' v: term): u' = u.[t .: ids] -> Case (InjL t) u v ~> u'

  (** Reduction of a [Case] with a right injection *)
  | Beta_Case_InjR (t u v v': term): v' = v.[t .: ids] -> Case (InjR t) u v ~> v'

  where "t ~> t'" := (beta t t').

(** Reflexive and transitive closure of the β-reduction *)
Notation "t ~>* t'" := (beta* t t') (at level 70, t' at next level).


(** ** Properties of terms with β-reduction *)

(** Preservation of the β-reduction under any substitution. *)
Lemma beta_subst (t t': term) (σ: var -> term):
  t ~> t' -> t.[σ] ~> t'.[σ].
Proof.
  revert t' σ.

  induction t as [
    | ? IHs ? IHt | s IHs
    | s IHs t IHt | s IHs | s IHs
    | t IHt u IHu v IHv | s IHs | s IHs
  ].

  (* Classical λ-calculus *)
  - intros ? ? Hbeta.
    inv Hbeta.

  - intros ? ? Hbeta.
    inv Hbeta.
    + apply Beta_Subst; asimpl.
      reflexivity.

    + apply Beta_AppL.
      now apply IHs.

    + apply Beta_AppR.
      now apply IHt.

  - intros ? ? Hbeta.
    inv Hbeta.
    apply Beta_Lam.
    now apply IHs.

  (* Pairs and projections *)
  - intros ? ? Hbeta.
    inv Hbeta.
    + apply Beta_Pair1.
      now apply IHs.
    + apply Beta_Pair2.
      now apply IHt.

  - intros ? ? Hbeta.
    inv Hbeta.
    + apply Beta_ProjL.
      now apply IHs.
    + apply Beta_ProjL_Pair.

  - intros ? ? Hbeta.
    inv Hbeta.
    + apply Beta_ProjR.
      now apply IHs.
    + apply Beta_ProjR_Pair.

  (* Pattern matching and injections *)
  - intros ? ? Hbeta.
    inv Hbeta.
    + apply Beta_Case1.
      now apply IHt.
    + apply Beta_Case2.
      now apply IHu.
    + apply Beta_Case3.
      now apply IHv.

    + apply Beta_Case_InjL; asimpl.
      reflexivity.
    + apply Beta_Case_InjR; asimpl.
      reflexivity.

  - intros ? ? Hbeta.
    inv Hbeta.
    apply Beta_InjL.
    now apply IHs.

  - intros ? ? Hbeta.
    inv Hbeta.
    apply Beta_InjR.
    now apply IHs.
Qed.

Ltac apply_step Hred Hstep :=
  induction Hstep; [
    apply rt_step; now apply Hred |
    apply rt_refl |
    eapply rt_trans; eassumption
  ].

(** *** Properties of β* *)

Lemma beta_star_context_unary (f: term -> term) (s s': term):
  (forall (s s': term), s ~> s' -> f s ~> f s') ->
  s ~>* s' -> f s ~>* f s'.
Proof.
  intros Hred Hstep.
  apply_step Hred Hstep.
Qed.

Lemma beta_star_context_binary (f: term -> term -> term) (s s' t t': term):
  (forall (s s' t: term), s ~> s' -> f s t ~> f s' t) ->
  (forall (s t t': term), t ~> t' -> f s t ~> f s t') ->
  s ~>* s' -> t ~>* t' -> f s t ~>* f s' t'.
Proof.
  intros Hred1 Hred2 Hstep1 Hstep2.

  apply rt_trans with (f s' t).
  { apply_step Hred1 Hstep1. }

  apply_step Hred2 Hstep2.
Qed.

Lemma beta_star_context_ternary (f: term -> term -> term -> term) (s s' t t' u u': term):
  (forall (s s' t u: term), s ~> s' -> f s t u ~> f s' t u) ->
  (forall (s t t' u: term), t ~> t' -> f s t u ~> f s t' u) ->
  (forall (s t u u': term), u ~> u' -> f s t u ~> f s t u') ->
  s ~>* s' -> t ~>* t' -> u ~>* u' -> f s t u ~>* f s' t' u'.
Proof.
  intros Hred1 Hred2 Hred3 Hstep1 Hstep2 Hstep3.

  apply rt_trans with (f s' t u).
  { apply_step Hred1 Hstep1. }

  apply rt_trans with (f s' t' u).
  { apply_step Hred2 Hstep2. }

  apply_step Hred3 Hstep3.
Qed.

Lemma beta_star_lam (s s': term):
  s ~>* s' ->
  Lam s ~>* Lam s'.
Proof.
  apply beta_star_context_unary.
  apply Beta_Lam.
Qed.

Lemma beta_star_app (s s' t t': term):
  s ~>* s' -> t ~>* t' ->
  App s t ~>* App s' t'.
Proof.
  apply beta_star_context_binary.
  - apply Beta_AppL.
  - apply Beta_AppR.
Qed.

Lemma beta_star_case (s s' t t' u u': term):
  s ~>* s' -> t ~>* t' -> u ~>* u' ->
  Case s t u ~>* Case s' t' u'.
Proof.
  apply beta_star_context_ternary.
  - apply Beta_Case1.
  - apply Beta_Case2.
  - apply Beta_Case3.
Qed.
