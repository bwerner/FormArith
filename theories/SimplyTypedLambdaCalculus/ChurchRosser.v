(**
  This file contains a complete proof of the confluence of the λ-calculus. More
  precisely, this means that the β-reduction on λ-terms satisfies the
  Church-Rosser propery.
*)

From FormArith.SimplyTypedLambdaCalculus Require Import Term.

(** * λ-calculus verifies the Church-Rosser property *)

(** ** Definitions *)

(** *** Local confluence

  A rewrite rule → is said to be locally confluent if:
  ∀ t u v, t → u ∧ t → v ⇒ ∃ w, u → w ∧ v → w.
*)
Definition local_confluence (P: term -> term -> Prop): Prop :=
  forall (t u v: term),
    P t u ->
    P t v ->
    exists (w : term), P u w /\ P v w.

(** *** Church-Rosser propery

  It is defined as the local confluence for the reflexive and transitive
  closure of the rewrite rule.
*)
Definition CR (P: term -> term -> Prop) := local_confluence P*.

(** Notation for the parallel reduction. *)
Reserved Notation "t >=> t'" (at level 60).

(** *** Parallel reduction

  This is a rewrite rule that is morally the same as appliying as much rewrite
  rules with the β-reduction as possible as each step.
*)
Inductive par_red: term -> term -> Prop :=
  (** Parallel substitution rule. *)
  | ParRed_Subst (s s' t t': term):
    s >=> s' ->
    t >=> t' ->
    App (Lam s) t >=> s'.[t'/]

  (** A variable can be reduced as itself. *)
  | ParRed_Var (v: var): (Var v) >=> (Var v)

  (** Parallel substitution of the application. *)
  | ParRed_App (s s' t t': term) :
    s >=> s' ->
    t >=> t' ->
    App s t >=> App s' t'

  (** Parallel substitution of the λ-abstraction. *)
  | ParRed_Lam (t t': term) :
    t >=> t' ->
    Lam t >=> Lam t'

  (** Parallel substitution of the pair. *)
  | ParRed_Pair (s s' t t': term):
    s >=> s' ->
    t >=> t' ->
    Pair s t >=> Pair s' t'

  (** Parallel substitution of π1. *)
  | ParRed_ProjL (s s': term):
    s >=> s' ->
    ProjL s >=> ProjL s'

  (** Parallel substitution of π2. *)
  | ParRed_ProjR (s s': term):
    s >=> s' ->
    ProjR s >=> ProjR s'

  (** Parallel substitution of the left projection of a pair. *)
  | ParRed_ProjL_Pair (s s' t: term):
    s >=> s' ->
    ProjL (Pair s t) >=> s'

  (** Parallel substitution of the right projection of a pair. *)
  | ParRed_ProjR_Pair (s t t': term):
    t >=> t' ->
    ProjR (Pair s t) >=> t'

  (** Parallel substitution of δ. *)
  | ParRed_Case (s s' t t' u u': term):
    s >=> s' ->
    t >=> t' ->
    u >=> u' ->
    Case s t u >=> Case s' t' u'

  (** Parallel substitution of i. *)
  | ParRed_InjL (s s': term):
    s >=> s' ->
    InjL s >=> InjL s'

  (** Parallel substitution of j. *)
  | ParRed_InjR (s s': term):
    s >=> s' ->
    InjR s >=> InjR s'

  (** Parallel substitution of the left case in a pattern matching. *)
  | ParRed_Case_InjL (s s' t t' u: term):
    s >=> s' ->
    t >=> t' ->
    Case (InjL s) t u >=> t'.[s'/]

  (** Parallel substitution of the right case in a pattern matching. *)
  | ParRed_Case_InjR (s s' t u u': term):
    s >=> s' ->
    u >=> u' ->
    Case (InjR s) t u >=> u'.[s'/]

  where "t >=> t'" := (par_red t t').

(** Reflexive and transitive closure of the parallel reduction. *)
Notation "t >=>* t'" := (par_red* t t') (at level 70, t' at next level).


(**
  Returns the term that is as reduced as possible regarding the parallel
  reduction.
*)
Fixpoint par_red_max_reduction (t: term): term :=
  match t with
  | Var v => Var v
  | App (Lam t) u => (par_red_max_reduction t).[(par_red_max_reduction u)/]
  | App t u => App (par_red_max_reduction t) (par_red_max_reduction u)
  | Lam t => Lam (par_red_max_reduction t)
  | Pair s t => Pair (par_red_max_reduction s) (par_red_max_reduction t)
  | ProjL (Pair s t) => par_red_max_reduction s
  | ProjR (Pair s t) => par_red_max_reduction t
  | ProjL s => ProjL (par_red_max_reduction s)
  | ProjR s => ProjR (par_red_max_reduction s)
  | InjL s => InjL (par_red_max_reduction s)
  | InjR s => InjR (par_red_max_reduction s)
  | Case (InjL s) t u => (par_red_max_reduction t).[(par_red_max_reduction s)/]
  | Case (InjR s) t u => (par_red_max_reduction u).[(par_red_max_reduction s)/]
  | Case s t u => Case (par_red_max_reduction s) (par_red_max_reduction t) (par_red_max_reduction u)
  end.

Definition replace_lambda (f: term -> term) (s u: term): term :=
  match s with
  | Lam s' => f s'
  | _ => u
  end.

Definition replace_pair (f: term -> term -> term) (s u: term): term :=
  match s with
  | Pair s t => f s t
  | _ => u
  end.

Definition replace_inj (f1 f2: term -> term) (s u: term): term :=
  match s with
  | InjL s' => f1 s'
  | InjR s' => f2 s'
  | _ => u
  end.


(** ** Properties *)

(** Reflexitivity of the parallel reduction. *)
Lemma par_red_refl (t: term):
  t >=> t.
Proof.
  induction t.
  - apply ParRed_Var.
  - now apply ParRed_App.
  - now apply ParRed_Lam.
  - now apply ParRed_Pair.
  - now apply ParRed_ProjL.
  - now apply ParRed_ProjR.
  - now apply ParRed_Case.
  - now apply ParRed_InjL.
  - now apply ParRed_InjR.
Qed.

(** The β-reduction is included in the parallel reduction. *)
Lemma beta_to_par_red (s t: term):
  s ~> t -> s >=> t.
Proof.
  induction 1.
  - rewrite H.
    apply ParRed_Subst.
    all: apply par_red_refl.

  - apply ParRed_App; [ assumption |].
    apply par_red_refl.

  - apply ParRed_App; [| assumption ].
    apply par_red_refl.

  - now apply ParRed_Lam.

  - apply ParRed_Pair; [ assumption |].
    apply par_red_refl.

  - apply ParRed_Pair; [| assumption ].
    apply par_red_refl.

  - now apply ParRed_ProjL.
  - now apply ParRed_ProjR.

  - apply ParRed_ProjL_Pair.
    apply par_red_refl.

  - apply ParRed_ProjR_Pair.
    apply par_red_refl.

  - apply ParRed_Case; [ assumption | | ].
    all: apply par_red_refl.

  - apply ParRed_Case; [ | assumption | ].
    all: apply par_red_refl.

  - apply ParRed_Case; [ | | assumption ].
    all: apply par_red_refl.

  - now apply ParRed_InjL.
  - now apply ParRed_InjR.

  - subst.
    apply ParRed_Case_InjL.
    all: apply par_red_refl.

  - subst.
    apply ParRed_Case_InjR.
    all: apply par_red_refl.
Qed.

(** The parallel reduction is stable under substitutions. *)
Lemma par_red_subst (t t': term) (σ: var -> term):
  t >=> t' ->
  t.[σ] >=> t'.[σ].
Proof.
  intros H.
  revert σ.

  induction H as [
    s s' t t' ? IHs ? IHt
    | v
    | s s' t t' par_red_s_s' IHs par_red_t_t' IHt
    | s s' par_red_s_s' IHs
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | s s' _ IHs
    | s s' t _ IHs
    | s t t' _ IHt
    | s s' t t' u u' _ IHs _ IHt _ IHu
    | s s' _ IHs
    | s s' _ IHs
    | s s' t t' u _ IHs _ IHt
    | s s' t u u' _ IHs _ IHu
  ]; intros σ; asimpl.

  - pose proof (ParRed_Subst s.[up σ] s'.[up σ] t.[σ] t'.[σ]) as HParRed.
    asimpl in HParRed.
    apply HParRed.
    + apply IHs.
    + apply IHt.

  - apply par_red_refl.

  - apply ParRed_App.
    + apply IHs.
    + apply IHt.

  - apply ParRed_Lam; asimpl.
    apply IHs.

  - apply ParRed_Pair.
    + apply IHs.
    + apply IHt.

  - apply ParRed_ProjL.
    apply IHs.

  - apply ParRed_ProjR.
    apply IHs.

  - apply ParRed_ProjL_Pair.
    apply IHs.

  - apply ParRed_ProjR_Pair.
    apply IHt.

  - apply ParRed_Case.
    + apply IHs.
    + apply IHt.
    + apply IHu.

  - apply ParRed_InjL.
    apply IHs.

  - apply ParRed_InjR.
    apply IHs.

  - pose proof (ParRed_Case_InjL s.[σ] s'.[σ] t.[up σ] t'.[up σ] u.[up σ]) as HParRed.
    asimpl in HParRed.
    apply HParRed.
    + apply IHs.
    + apply IHt.

  - pose proof (ParRed_Case_InjR s.[σ] s'.[σ] t.[up σ] u.[up σ] u'.[up σ]) as HParRed.
    asimpl in HParRed.
    apply HParRed.
    + apply IHs.
    + apply IHu.
Qed.

Lemma par_red_subst_up (σ σ': var -> term):
  (forall (v: var), σ v >=> σ' v) ->
    forall (v: var), up σ v >=> up σ' v.
Proof.
  intros H.
  destruct v.
  - apply par_red_refl.
  - asimpl.
    apply par_red_subst.
    apply H.
Qed.

Lemma par_red_subst_par_red (s t: term) (σ σ': var -> term):
  (forall v: var, σ v >=> σ' v) ->
  s >=> t -> s.[σ] >=> t.[σ'].
Proof.
  intros Hv H.
  revert σ σ' Hv.

  induction H as [
    s s' t t' _ IHs _ IHt
    | v
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | s s' _ IHs
    | s s' t _ IHs
    | s t t' _ IHt
    | s s' t t' u u' _ IHs _ IHt _ IHu
    | s s' _ IHs
    | s s' _ IHs
    | s s' t t' u _ IHs _ IHt
    | s s' t u u' _ IHs _ IHu
  ]; intros σ σ' Hv; asimpl.

  - pose proof (ParRed_Subst s.[up σ] s'.[up σ'] t.[σ] t'.[σ']) as HParRed.
    asimpl in HParRed.
    apply HParRed.
    + apply IHs.
      now apply par_red_subst_up.
    + now apply IHt.

  - apply Hv.

  - apply ParRed_App.
    + now apply IHs.
    + now apply IHt.

  - apply ParRed_Lam.
    apply IHs.
    now apply par_red_subst_up.

  - apply ParRed_Pair.
    + now apply IHs.
    + now apply IHt.

  - apply ParRed_ProjL.
    now apply IHs.

  - apply ParRed_ProjR.
    now apply IHs.

  - apply ParRed_ProjL_Pair.
    now apply IHs.

  - apply ParRed_ProjR_Pair.
    now apply IHt.

  - apply ParRed_Case.
    + now apply IHs.
    + apply IHt.
      now apply par_red_subst_up.
    + apply IHu.
      now apply par_red_subst_up.

  - apply ParRed_InjL.
    now apply IHs.

  - apply ParRed_InjR.
    now apply IHs.

  - pose proof (ParRed_Case_InjL s.[σ] s'.[σ'] t.[up σ] t'.[up σ'] u.[up σ]) as HParRed.
    asimpl in HParRed.
    apply HParRed.
    + now apply IHs.
    + apply IHt.
      now apply par_red_subst_up.

  - pose proof (ParRed_Case_InjR s.[σ] s'.[σ'] t.[up σ] u.[up σ] u'.[up σ']) as HParRed.
    asimpl in HParRed.
    apply HParRed.
    + now apply IHs.
    + apply IHu.
      now apply par_red_subst_up.
Qed.

(**
  The parallel reduction is included in the reflexive and transitive closure of
  the β-reduction.
*)
Lemma par_red_to_beta_star (s t: term):
  s >=> t -> s ~>* t.
Proof.
  intros H.
  induction H as [
    s s' t t' _ beta_star_s_s' _ beta_star_t_t'
    | v
    | s s' t t' _ beta_star_s_s' _ beta_star_t_t'
    | s s' _ beta_star_s_s'
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | s s' _ IHs
    | s s' t _ IHs
    | s t t' _ IHt
    | s s' t t' u u' _ IHs _ IHt _ IHu
    | s s' _ IHs
    | s s' _ IHs
    | s s' t t' u _ IHs _ IHt
    | s s' t u u' _ IHs _ IHu
  ].

  - apply rt_trans with (App (Lam s') t).
    { apply beta_star_app.
      - now apply beta_star_lam.
      - apply rt_refl. }

    apply rt_trans with (App (Lam s') t').
    { apply beta_star_app; [| assumption ].
      apply rt_refl. }

    apply rt_step.
    now apply Beta_Subst.

  - apply rt_refl.

  - now apply beta_star_app.

  - now apply beta_star_lam.

  - apply beta_star_context_binary; [| | assumption .. ].
    + apply Beta_Pair1.
    + apply Beta_Pair2.

  - apply beta_star_context_unary; [| assumption ].
    apply Beta_ProjL.

  - apply beta_star_context_unary; [| assumption ].
    apply Beta_ProjR.

  - apply rt_trans with s; [| assumption ].
    apply rt_step.
    apply Beta_ProjL_Pair.

  - apply rt_trans with t; [| assumption ].
    apply rt_step.
    apply Beta_ProjR_Pair.

  - now apply beta_star_case.

  - apply beta_star_context_unary; [| assumption ].
    apply Beta_InjL.

  - apply beta_star_context_unary; [| assumption ].
    apply Beta_InjR.

  - apply rt_trans with (Case (InjL s') t u).
    { apply beta_star_case.
      { apply beta_star_context_unary; [| assumption ].
        apply Beta_InjL. }
      all: apply rt_refl. }

    apply rt_trans with (Case (InjL s') t' u).
    { apply beta_star_case; [| assumption |].
      all: apply rt_refl. }

    apply rt_step.
    now apply Beta_Case_InjL.

  - apply rt_trans with (Case (InjR s') t u).
    { apply beta_star_case.
      { apply beta_star_context_unary; [| assumption ].
        apply Beta_InjR. }
      all: apply rt_refl. }

    apply rt_trans with (Case (InjR s') t u').
    { apply beta_star_case; [| | assumption ].
      all: apply rt_refl. }

    apply rt_step.
    now apply Beta_Case_InjR.
Qed.

(**
  The parallel reduction is exactly the reflexive and transitive closure of the
  β-reduction.
*)
Lemma beta_star_equiv_par_red_star (s t: term):
  s ~>* t <-> s >=>* t.
Proof.
  split; intros H.

  - induction H as [ | | ? t ].
    + apply rt_step.
      now apply beta_to_par_red.
    + apply rt_refl.
    + now apply rt_trans with t.

  - induction H as [ | | ? t ].
    + now apply par_red_to_beta_star.
    + apply rt_refl.
    + now apply rt_trans with t.
Qed.

Lemma lam_match (s u: term) (f: term -> term):
  (exists s', s = Lam s' /\ replace_lambda f s u = f s') \/
    (replace_lambda f s u = u /\ ~ exists s', s = Lam s').
Proof.
  destruct s as [| | s | | | | | |]; simpl.

  (* Lam *)
  3: { left. now exists s. }

  all: right.
  all: split; [ reflexivity |].
  all: intros [? ?]; discriminate.
Qed.

Lemma pair_match (s u: term) (f: term -> term -> term):
  (exists s' t', s = Pair s' t' /\ replace_pair f s u = f s' t') \/
    (replace_pair f s u = u /\ ~ exists s' t', s = Pair s' t').
Proof.
  destruct s as [| | | s1 s2 | | | | |]; simpl.

  (* Pair *)
  4: { left. now exists s1, s2. }

  all: right.
  all: split; [ reflexivity |].
  all: intros [? [? ?]]; discriminate.
Qed.

Lemma inj_match (s u: term) (f1 f2: term -> term):
  (exists s', s = InjL s' /\ replace_inj f1 f2 s u = f1 s') \/
  (exists s', s = InjR s' /\ replace_inj f1 f2 s u = f2 s') \/
    (replace_inj f1 f2 s u = u /\ ~ (exists s', s = InjL s') /\ ~ (exists s', s = InjR s')).
Proof.
  destruct s.

  (* InjL/InjR *)
  8: { left. now exists s. }
  8: { right. left. now exists s. }

  all: right; right.
  all: split; [ reflexivity |].
  all: split; intros [? ?]; discriminate.
Qed.

(** Link between the parallel reduction and the function [par_red_max_reduction]. *)
Lemma max_par_red (t t': term):
  t >=> t' -> t' >=> par_red_max_reduction t.
Proof.
  induction 1 as [
    s s' t t' _ IHs _ IHt
    | v
    | s s' t t' par_red_s_s' IHs _ IHt
    | s s' _ IHs
    | s s' t t' _ IHs _ IHt
    | s s' par_red_s_s' IHs
    | s s' par_red_s_s' IHs
    | s s' t par_red_s_s' IHs
    | s t t' _ IHt
    | s s' t t' u u' par_red_s_s' IHs _ IHt _ IHu
    | s s' _ IHs
    | s s' _ IHs
    | s s' t t' u _ IHs _ IHt
    | s s' t u u' _ IHs _ IHu
  ]; asimpl.

  - apply par_red_subst_par_red; [| assumption ].
    intros []; asimpl; [ assumption |].
    now apply par_red_refl.

  - apply par_red_refl.

  - set (f := fun s' => (par_red_max_reduction s').[par_red_max_reduction t/]).
    destruct (lam_match s (App (par_red_max_reduction s) (par_red_max_reduction t)) f)
      as [[u [H1 H2]] | [H1 H2]]; subst; simpl in IHs.

    + inv par_red_s_s'; inv IHs.
      now apply ParRed_Subst.

    + destruct s.
      3: { exfalso. apply H2. now exists s. }
      all: now apply ParRed_App.

  - now apply ParRed_Lam.
  - now apply ParRed_Pair.

  - set (f := fun (s t : term) => par_red_max_reduction s).
    destruct (pair_match s (ProjL (par_red_max_reduction s)) f)
      as [[u [v [H1 H2]]] | [H1 H2]]; subst; simpl in IHs.

    + inv par_red_s_s'; inv IHs.
      now apply ParRed_ProjL_Pair.

    + destruct s.
      4: { exfalso. apply H2. now exists s1, s2. }
      all: now apply ParRed_ProjL.

  - set (f := fun (s t : term) => par_red_max_reduction s).
    destruct (pair_match s (ProjR (par_red_max_reduction s)) f)
      as [[u [v [H1 H2]]] | [H1 H2]]; subst; simpl in IHs.

    + inv par_red_s_s'; inv IHs.
      now apply ParRed_ProjR_Pair.

    + destruct s.
      4: { exfalso. apply H2. now exists s1, s2. }
      all: now apply ParRed_ProjR.

  - assumption.
  - assumption.

  - set (f1 := fun s0 => (par_red_max_reduction t).[par_red_max_reduction s0/]).
    set (f2 := fun s0 => (par_red_max_reduction u).[par_red_max_reduction s0/]).

    destruct (inj_match s (Case (par_red_max_reduction s)
                             (par_red_max_reduction t) (par_red_max_reduction u)) f1 f2)
      as [[v [H1 H2]] | [[v [H1 H2]] | [H1 [H2 H3]] ]]; subst; simpl in IHs.

    + inv par_red_s_s'; inv IHs.
      now apply ParRed_Case_InjL.

    + inv par_red_s_s'; inv IHs.
      now apply ParRed_Case_InjR.

    + destruct s.
      9: { exfalso. apply H3. now exists s. }
      8: { exfalso. apply H2. now exists s. }
      all: now apply ParRed_Case.

  - now apply ParRed_InjL.
  - now apply ParRed_InjR.

  - apply par_red_subst_par_red; [| assumption ].
    intros [| v ]; simpl; [ assumption |].
    apply par_red_refl.

  - apply par_red_subst_par_red; [| assumption ].
    intros [| v ]; simpl; [ assumption |].
    apply par_red_refl.
Qed.

(** The parallel reduction is locally confluent. *)
Lemma local_confluence_par_red: local_confluence par_red.
Proof.
  intros t u v Hu Hv.
  exists (par_red_max_reduction t).
  split; now apply max_par_red.
Qed.

Lemma par_red_left_cr (t u v: term):
  par_red t u ->
  par_red* t v ->
  exists (w: term), par_red* u w /\ par_red v w.
Proof.
  intros Hu Hv.
  revert u Hu.

  induction Hv as [ t v Hv | t | t v v' Hv IHv Hv' IHv']; intros u Hu.
  - destruct (local_confluence_par_red t u v Hu Hv) as [w [H1 H2]].
    exists w.
    split; [| assumption ].
    now apply rt_step.

  - exists u.
    split; [| assumption ].
    apply rt_refl.

  - specialize (IHv _ Hu) as [u' [H1 H2]].
    specialize (IHv' _ H2) as [w [H3 H4]].
    exists w.
    split; [| assumption ].
    now apply rt_trans with u'.
Qed.

(** The parallel reduction satisfies the Church-Rosser property. *)
Lemma par_red_cr: CR par_red.
Proof.
  intros t u v Hu Hv.
  revert v Hv.

  induction Hu as [ t u Hu | t | t u u' Hu IHu Hu' IHu' ]; intros v Hv.
  - destruct (par_red_left_cr t u v Hu Hv) as [w [H1 H2]].
    exists w.
    split; [ assumption |].
    now apply rt_step.

  - exists v.
    split; [ assumption |].
    apply rt_refl.

  - specialize (IHu _ Hv) as [v' [H1 H2]].
    specialize (IHu' _ H1) as [w [H3 H4]].
    exists w.
    split; [ assumption |].
    now apply rt_trans with v'.
Qed.

(** The β-reduction satisfies the Church-Rosser property. *)
Theorem ChurchRosser: CR beta.
Proof.
  intros t u v Hu Hv.
  rewrite beta_star_equiv_par_red_star in Hu, Hv.

  specialize (par_red_cr t u v Hu Hv) as [w [H1 H2]].
  rewrite <- beta_star_equiv_par_red_star in H1, H2.

  exists w.
  now split.
Qed.
