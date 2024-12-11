(**
  This file contains a complete proof a the strong normalisation of the
  simply-typed λ-calculus.
*)

From FormArith.SimplyTypedLambdaCalculus Require Import Term Typing.

(** * Strong normalisation of the simply-typed λ-calculus *)

(** ** Definitions *)

(** *** Strong normalisation

  Intuitively, a [term] is strongly normalising if all of its successor for the
  β-reduction are also strongly normalising.

  This definition is equivalent but easier to deal with in Rocq than the usual
  definition "There is no infinite path starting with this term".
*)
Inductive SN: term -> Prop :=
  | Strong (t: term) :
      (forall (t': term), t ~> t' -> SN t') -> SN t.

(** *** Reducibility

  Creates a proof of the strong normalisation of a term [t] based on the shape
  of its type [A].
*)
Fixpoint reducible (A: type) (t: term): Prop :=
  match A with
  | Base => SN t
  | Arr A B => forall (u: term), reducible A u -> reducible B (App t u)
  | Prod A B => reducible A (ProjL t) /\ reducible B (ProjR t)
  | Sum A B =>
      SN t /\
      (forall u, t ~>* InjL u -> reducible A u) /\
      (forall v, t ~>* InjR v -> reducible B v)
  end.

(** *** Neutral terms

  A term is said to be "neutral" if it can be reduced.
*)
Definition neutral (t: term): Prop :=
  match t with
  | Lam _ | Pair _ _ | InjL _ | InjR _ => False
  | _ => True
  end.

(** *** Direct sub-terms

  [sub_term t1 t2] holds if and only if [t1] is a direct sub-term of [t2].
*)
Inductive sub_term: term -> term -> Prop :=
  (** t1 is a sub-term of t1 t2 *)
  | Sub_App1 (t1 t2: term) : sub_term t1 (App t1 t2)
  
  (** t2 is a sub-term of t1 t2 *)
  | Sub_App2 (t1 t2: term) : sub_term t2 (App t1 t2)
  
  (** t is a sub-term of λ t *)
  | Sub_Lam (t: term) : sub_term t (Lam t)
  
  (** t1 is a sub-term of (t1, t2) *)
  | Sub_Pair1 (t1 t2: term): sub_term t1 (Pair t1 t2)
  
  (** t2 is a sub-term of (t1, t2) *)
  | Sub_Pair2 (t1 t2: term): sub_term t2 (Pair t1 t2)
  
  (** t is a sub-term of π1(t) *)
  | Sub_ProjL (t: term): sub_term t (ProjL t)
  
  (** t is a sub-term of π2(t) *)
  | Sub_ProjR (t: term): sub_term t (ProjR t)
  
  (** t1 is a sub-term of δ(t1, t2, t3) *)
  | Sub_Case1 (t1 t2 t3: term): sub_term t1 (Case t1 t2 t3)
  
  (** t2 is a sub-term of δ(t1, t2, t3) *)
  | Sub_Case2 (t1 t2 t3: term): sub_term t2 (Case t1 t2 t3)
  
  (** t3 is a sub-term of δ(t1, t2, t3) *)
  | Sub_Case3 (t1 t2 t3: term): sub_term t3 (Case t1 t2 t3)
  
  (** t is a sub-term of i(t) *)
  | Sub_InjL (t: term): sub_term t (InjL t)
  
  (** t is a sub-term of j(t) *)
  | Sub_InjR (t: term): sub_term t (InjR t).


(** ** Properties *)

Lemma SN_lam (t: term):
  SN t -> SN (Lam t).
Proof.
  revert t.

  apply SN_ind; intros ? _ H.
  apply Strong; intros ? Hbeta.
  inv Hbeta.
  now apply H.
Qed.

(**
  If a term is strongly normalising, then all of its direct sub-terms are
  strongly normalising.
*)
Lemma SN_sub_term (t: term):
  SN t -> forall (t': term), sub_term t' t -> SN t'.
Proof.
  induction 1 as [ ? _ IH ].
  inversion 1; subst.
  all: apply Strong; intros u ?.

  all: match goal with
       | H: sub_term _ (App ?t ?t') |- _ => rename t into t1; rename t' into t2
       | H: _ |- _ => idtac
       end.

  (** Classical λ-calculus *)
  - apply IH with (App u t2).
    + now apply Beta_AppL.
    + apply Sub_App1.

  - apply IH with (App t1 u).
    + now apply Beta_AppR.
    + apply Sub_App2.

  - apply IH with (Lam u).
    + now apply Beta_Lam.
    + apply Sub_Lam.

  (** Pairs and projections *)
  - apply IH with (Pair u t2).
    + now apply Beta_Pair1.
    + apply Sub_Pair1.

  - apply IH with (Pair t1 u).
    + now apply Beta_Pair2.
    + apply Sub_Pair2.

  - apply IH with (ProjL u).
    + now apply Beta_ProjL.
    + apply Sub_ProjL.

  - apply IH with (ProjR u).
    + now apply Beta_ProjR.
    + apply Sub_ProjR.

  (** Sum types *)
  - apply IH with (Case u t2 t3).
    + now apply Beta_Case1.
    + apply Sub_Case1.

  - apply IH with (Case t1 u t3).
    + now apply Beta_Case2.
    + apply Sub_Case2.

  - apply IH with (Case t1 t2 u).
    + now apply Beta_Case3.
    + apply Sub_Case3.

  - apply IH with (InjL u).
    + now apply Beta_InjL.
    + apply Sub_InjL.

  - apply IH with (InjR u).
    + now apply Beta_InjR.
    + apply Sub_InjR.
Qed.

Lemma SN_var_app (t: term) (n: var):
  SN (App t (Var n)) -> SN t.
Proof.
  intros ?.
  apply (SN_sub_term (App t (Var n))); [ assumption |].
  apply Sub_App1.
Qed.

Lemma SN_inverted (t: term):
  SN t -> forall (t': term), t ~> t' -> SN t'.
Proof.
  now inversion 1.
Qed.

(**
  Links between reducibility, neutrality and strong normalisation:

  - every reducible term is strongly normalising
  - if t is reducible with type A, and if t → u, then u is reducible with
    type A
  - if t is neutral and every term into which t can be β-reduced is reducible
    with type A, then t is reducible with type A.
*)
Lemma reducible_is_SN (A : type):
  (forall (t: term), reducible A t -> SN t) /\
    (forall (t u: term), reducible A t -> t ~> u -> reducible A u) /\
    (forall (t: term), neutral t -> (forall (t': term), t ~> t' -> reducible A t') -> reducible A t).
Proof.
  induction A as [
    | A [IHA1 [IHA2 IHA3]] B [IHB1 [IHB2 IHB3]]
    | A [IHA1 [IHA2 IHA3]] B [IHB1 [IHB2 IHB3]]
    | A [IHA1 [IHA2 IHA3]] B [IHB1 [IHB2 IHB3]]
  ].

  - split; [| split ]; simpl.
    + now intros.

    + intros t u ? ?.
      apply Strong; intros.
      apply SN_inverted with u; [| assumption ].
      now apply SN_inverted with t.

    + intros.
      now apply Strong.

  - split; [| split ]; simpl.
    + intros ? Hred.
      apply Strong; intros.
      apply SN_inverted with t; [| assumption ].
      apply SN_var_app with 0.

      apply IHB1.
      apply Hred.
      apply IHA3; [ exact I |].
      inversion 1.

    + intros t ? IHred ? u Hred.
      apply IHB2 with (App t u).
      * apply IHred.
        apply Hred.
      * now apply Beta_AppL.

    + intros ? ? Hredt ? Hredu.
      apply IHA1 in Hredu as HSNu.

      induction HSNu as [ u _ IHu ].
      apply IHB3; [ exact I |].

      inversion 1; subst.
      * contradiction.
      * now apply Hredt.
      * apply IHu; [ assumption |].
        now apply IHA2 with u.

  - split; [| split ]; simpl.
    + intros t [Hred _].
      apply IHA1 in Hred.
      apply SN_sub_term with (t' := t) in Hred; [ assumption |].
      apply Sub_ProjL.

    + intros t u [Hred1 Hred2] Hstep.
      split.
      * apply (IHA2 (ProjL t) _ Hred1).
        now apply Beta_ProjL.
      * apply (IHB2 (ProjR t) _ Hred2).
        now apply Beta_ProjR.

    + intros t Hneu H.
      split; [ apply IHA3 | apply IHB3 ]; simpl.
      all: try exact I.
      all: intros t' Hstep.
      all: inv Hstep; [| destruct Hneu ].
      all: apply (H s' H1).

  - split; [| split ]; simpl.
    + intros t [HSN _].
      apply HSN.

    + intros t u [Hredt1 [Hredt2 Hredt3]] Hbeta.
      split.
      { now apply (SN_inverted t Hredt1). }

      split; intros; [ apply Hredt2 | apply Hredt3 ].
      all: apply rt_trans with u; [| assumption ].
      all: now apply rt_step.

    + intros t Hneu H.
      split.
      { apply Strong; intros. now apply H. }

      split.
      all: intros u Hbeta.
      all: rewrite clos_rt_rt1n_iff in Hbeta.
      all: inv Hbeta; [ destruct Hneu |].
      all: apply H with y; [ assumption |].
      all: now apply clos_rt_rt1n_iff.
Qed.

(** Strongly normalising is closed under substitutions. *)
Lemma SN_subst (t: term) (σ: var -> term):
  SN t -> forall (u: term), t = u.[σ] -> SN u.
Proof.
  induction 1 as [? _ IHt]; intros; subst.
  apply Strong; intros t ?.
  apply IHt with t.[σ].
  - now apply beta_subst.
  - reflexivity.
Qed.

(** Double induction principle on terms. *)
Lemma SN_ind_pair (P : term -> term -> Prop):
  (forall t u, (forall t' u', ((t = t' /\ u ~> u') \/ (t ~> t' /\ u = u')) -> P t' u') -> P t u) ->
    forall t u, SN t -> SN u -> P t u.
Proof.
  intros IH ? ? Hsnt.
  revert u.

  induction Hsnt as [? _ IHt].
  intros ? Hsnt.

  induction Hsnt as [? ? IHv].
  apply IH.

  intros ? ? [[? ?] | [? ?]]; subst.
  - now apply IHv.
  - apply IHt; [ assumption |].
    now apply Strong.
Qed.

(** Triple induction principle on terms. *)
Lemma SN_triple_ind (P : term -> term -> term -> Prop):
  (forall t u v,
    (forall t' u' v',
      ((t = t' /\ u = u' /\ v ~> v') \/
        (t = t' /\ u ~> u' /\ v = v') \/
        (t ~> t' /\ u = u' /\ v = v')) -> P t' u' v') -> P t u v) ->
  forall t u v, SN t -> SN u -> SN v -> P t u v.
Proof.
  intros IH t u v Hsnt.
  revert u v.

  induction Hsnt as [? _ IHt].
  intros u v Hsnu.

  revert v.
  induction Hsnu as [? HSNu IHu].

  intros v Hsnv.
  induction Hsnv as [? HSNv IHv].
  apply IH.

  intros ? ? ? [[? [? ?]] | [[? [? ?]] | [? [? ?]]]]; subst.
  - now apply IHv.

  - apply IHu; [ assumption |].
    apply Strong; intros.
    now apply HSNv.

  - apply IHt; [ assumption | |].
    + apply Strong; intros.
      now apply HSNu.
    + apply Strong; intros.
      now apply HSNv.
Qed.

Lemma reducible_abs (v: term) (A B: type):
  (forall (u: term), reducible A u -> reducible B v.[u/]) ->
    reducible (Arr A B) (Lam v).
Proof.
  intros Hred u Hredu.
  specialize (reducible_is_SN A) as [HA1 [HA2 HA3]].
  specialize (reducible_is_SN B) as [HB1 [HB2 HB3]].

  assert (HSNu: SN u) by now apply HA1.
  assert (HSNv: SN v).
  { apply SN_subst with v.[u/] (u .: ids); [| reflexivity ].
    apply HB1.
    now apply Hred. }

  revert Hred Hredu.
  apply SN_ind_pair with (t := v) (u := u).
  2: { apply HSNv. }
  2: { apply HSNu. }

  intros x y IH Hred Hredy.
  apply HB3; [ exact I |].
  intros t Hbeta.

  inv Hbeta.
  - now apply Hred.

  - inv H2.
    apply IH; [ .. | assumption ].
    { now right. }

    intros.
    apply HB2 with x.[u0/].
    + now apply Hred.
    + now apply beta_subst.

  - apply IH.
    + now left.
    + now apply Hred.
    + now apply HA2 with y.
Qed.

Lemma reducible_var (A: type) (x: var) (Γ: var -> type):
  Γ ⊢ Var x : A -> reducible A (Var x).
Proof.
  intros.
  specialize (reducible_is_SN A) as (_ & _ & HA3).
  apply HA3; [ exact I |].
  inversion 1.
Qed.

Lemma reducible_pair (A B: type) (u v: term):
  reducible A u ->
  reducible B v ->
  reducible (Prod A B) (Pair u v).
Proof.
  intros Hredu Hredv; simpl.

  specialize (reducible_is_SN A) as (HA1 & HA2 & HA3).
  specialize (reducible_is_SN B) as (HB1 & HB2 & HB3).

  assert (HSNu: SN u) by now apply HA1.
  assert (HSNv: SN v) by now apply HB1.

  revert Hredu Hredv.
  apply SN_ind_pair with (t := u) (u := v); [| assumption.. ].

  intros u' v' IH Hredu' Hredv'.
  split; [ apply HA3 | apply HB3 ]; simpl.
  all: try exact I.
  all: intros t' Hred.
  all: inv Hred; [| assumption ].
  all: inv H0.

  - apply IH; [| | assumption ].
    + now right.
    + now apply HA2 with u'.

  - apply IH; [| assumption |].
    + now left.
    + now apply HB2 with v'.

  - apply IH; [| | assumption ].
    + now right.
    + now apply HA2 with u'.

  - apply IH; [| assumption |].
    + now left.
    + now apply HB2 with v'.
Qed.

Lemma reducible_sum_injL (A B: type) (s: term):
  reducible A s ->
  reducible (Sum A B) (InjL s).
Proof.
  intros Hreds; simpl.

  specialize (reducible_is_SN A) as (HA1 & HA2 & HA3).
  assert (HSN: SN s) by now apply HA1.

  induction HSN as [s _ IH].
  split.
  { apply Strong; intros t' Hstep.
    inv Hstep.
    apply IH; [ assumption |].
    now apply HA2 with s. }

  all: split.
  all: intros ? Hbeta.
  all: rewrite clos_rt_rt1n_iff in Hbeta.
  all: inv Hbeta; try assumption.
  all: inv H.

  - apply (IH s'); [ assumption | |].
    + now apply HA2 with s.
    + now apply clos_rt_rt1n_iff.

  - apply (IH s'); [ assumption | |].
    + now apply HA2 with s.
    + now apply clos_rt_rt1n_iff.
Qed.

Lemma reducible_sum_injR (A B: type) (s: term):
  reducible B s ->
  reducible (Sum A B) (InjR s).
Proof.
  intros Hreds; simpl.

  specialize (reducible_is_SN B) as (HB1 & HB2 & HB3).
  assert (HSN: SN s) by now apply HB1.

  induction HSN as [s _ IH].
  split.
  { apply Strong; intros t' Hstep.
    inv Hstep.
    apply IH; [ assumption |].
    now apply HB2 with s. }

  all: split.
  all: intros ? Hbeta.
  all: rewrite clos_rt_rt1n_iff in Hbeta.
  all: inv Hbeta; try assumption.
  all: inv H.

  - apply (IH s'); [ assumption | |].
    + now apply HB2 with s.
    + now apply clos_rt_rt1n_iff.

  - apply (IH s'); [ assumption | |].
    + now apply HB2 with s.
    + now apply clos_rt_rt1n_iff.
Qed.

Lemma reducible_case (A B C: type) (t u v: term):
  reducible (Sum A B) t ->
  reducible (Arr A C) (Lam u) ->
  reducible (Arr B C) (Lam v) ->
  reducible C (Case t u v).
Proof.
  intros Hredt Hredu Hredv.

  specialize (reducible_is_SN (Arr A C)) as (HAC1 & HAC2 & HAC3).
  specialize (reducible_is_SN (Arr B C)) as (HBC1 & HBC2 & HBC3).
  specialize (reducible_is_SN (Sum A B)) as (H1 & H2 & H3).
  specialize (reducible_is_SN C) as (HC1 & HC2 & HC3).

  assert (HSNt: SN t) by now apply H1.
  assert (HSNu: SN u).
  { apply SN_sub_term with (Lam u).
    - now apply HAC1.
    - apply Sub_Lam. }

  assert (HSNv: SN v).
  { apply SN_sub_term with (Lam v).
    - now apply HBC1.
    - apply Sub_Lam. }

  revert Hredt Hredu Hredv.
  apply SN_triple_ind with (t := t) (u := u) (v := v); [| assumption.. ].

  intros t0 u0 v0 IH Hredt0 Hredu0 Hredv0.
  apply HC3; [ exact I |].

  intros t' Hstep.
  inv Hstep.

  - apply IH; [| | assumption.. ].
    + now right; right.
    + now apply H2 with t0.

  - apply IH; [| assumption | | assumption ].
    + now right; left.
    + apply HAC2 with (Lam u0); [ assumption |].
      now apply Beta_Lam.

  - apply IH; [ | assumption..  |].
    + now left.
    + apply HBC2 with (Lam v0); [ assumption |].
      now apply Beta_Lam.

  - assert (reducible C (App (Lam u0) t1)).
    { simpl in Hredu0.
      apply Hredu0.
      apply Hredt0.
      apply rt_refl. }

    apply HC2 with (App (Lam u0) t1); [ assumption |].
    now apply Beta_Subst.

  - assert (reducible C (App (Lam v0) t1)).
    { simpl in Hredv0.
      apply Hredv0.
      apply Hredt0.
      apply rt_refl. }

    apply HC2 with (App (Lam v0) t1); [ assumption |].
    now apply Beta_Subst.
Qed.

(**
  Conclusion of previous lemmas: if Γ and σ are such that for every variable
  x in Γ, σ(x) is reducible with type Γ(x), then Γ ⊢ t : A implies that t[σ] is
  reducible with type A.
*)
Lemma typing_is_reducible (Γ: var -> type) (σ: var -> term):
  (forall (x: var), reducible (Γ x) (σ x)) ->
    forall (A: type) (t: term), Γ ⊢ t : A -> reducible A t.[σ].
Proof.
  intros Hred A t.
  revert σ A Γ Hred.

  induction t; intros σ A Γ Hred.
  all: inversion 1; subst.
  - apply Hred.

  - apply IHt1 with (σ := σ) in H2; [| assumption ].
    apply IHt2 with (σ := σ) in H4; [| assumption ].
    now apply H2.

  - apply reducible_abs.
    intros u Hredu; asimpl.
    apply IHt with (A0 .: Γ); [| assumption ].
    intros [| x ]; simpl; [ assumption |].
    apply Hred.

  - apply reducible_pair.
    + now apply IHt1 with Γ.
    + now apply IHt2 with Γ.

  - apply (IHt σ (Prod A B) Γ Hred H1).
  - apply (IHt σ (Prod A0 A) Γ Hred H1).

  - simpl.
    apply reducible_case with A0 B.
    + now apply IHt with Γ.
    + apply reducible_abs.
      intros; asimpl.
      apply IHt0 with (A0 .: Γ); [| assumption ].
      intros [| x ]; simpl; [ assumption | apply Hred ].
    + apply reducible_abs.
      intros; asimpl.
      apply IHt1 with (B .: Γ); [| assumption ].
      intros [| x ]; simpl; [ assumption | apply Hred ].

  - replace ((InjL t).[σ]) with (InjL t.[σ]) by reflexivity.
    apply reducible_sum_injL.
    now apply IHt with Γ.

  - replace ((InjR t).[σ]) with (InjR t.[σ]) by reflexivity.
    apply reducible_sum_injR.
    now apply IHt with Γ.
Qed.

(**
  Strong normalisation of simply-typed λ-calculus: all typable terms are
  strongly normalising.

  This is a direct consequence of the previous lemma [typing_is_reducible].
*)
Corollary STLC_is_SN (A: type) (Γ: var -> type) (t: term):
  Γ ⊢ t : A -> SN t.
Proof.
  intros.
  apply (reducible_is_SN A).
  replace t with t.[ids] by apply subst_id.

  apply typing_is_reducible with Γ; [| assumption ].
  intros.

  apply reducible_var with Γ.
  now apply Typing_Var.
Qed.
