From FormArith.SimplyTypedLambdaCalculus Require Import Definitions.

Require Import Relations.Relations.


Inductive SN: term -> Prop :=
  | Strong (t: term) :
      (forall (t': term), t ~> t' -> SN t') -> SN t.

Locate "~>*".

Fixpoint reducible (A: type) (t: term): Prop :=
  match A with
  | Base => SN t
  | Arr A B => forall (u: term), reducible A u -> reducible B (App t u)
  | Prod A B => reducible A (Pr1 t) /\ reducible B (Pr2 t)
  | Sum A B =>
      SN t /\
      (forall u, t ~>* In1 u -> reducible A u) /\
      (forall v, t ~>* In2 v -> reducible B v)
  end.

Definition neutral (t: term): Prop :=
  match t with
  | Lam _ | Pair _ _ | In1 _ | In2 _ => False
  | _ => True
  end.

Inductive sub_term: term -> term -> Prop :=
  | Sub_app1 (t1 t2: term) : sub_term t1 (App t1 t2)
  | Sub_app2 (t1 t2: term) : sub_term t2 (App t1 t2)
  | Sub_lam (t: term) : sub_term t (Lam t)
  | Sub_pair1 (t1 t2: term): sub_term t1 (Pair t1 t2)
  | Sub_pair2 (t1 t2: term): sub_term t2 (Pair t1 t2)
  | Sub_pr1 (t: term): sub_term t (Pr1 t)
  | Sub_pr2 (t: term): sub_term t (Pr2 t)
  | Sub_pat1 (t1 t2 t3: term): sub_term t1 (Pat t1 t2 t3)
  | Sub_pat2 (t1 t2 t3: term): sub_term t2 (Pat t1 t2 t3)
  | Sub_pat3 (t1 t2 t3: term): sub_term t3 (Pat t1 t2 t3)
  | Sub_in1 (t: term): sub_term t (In1 t)
  | Sub_in2 (t: term): sub_term t (In2 t).

Lemma SN_lam (t: term):
  SN t -> SN (Lam t).
Proof.
  revert t.

  apply SN_ind; intros ? _ H.
  apply Strong; intros ? Hbeta.
  inversion Hbeta; subst.
  now apply H.
Qed.

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

  (** Classical Lambda calculus *)
  - apply IH with (App u t2).
    + now apply Beta_AppL.
    + apply Sub_app1.

  - apply IH with (App t1 u).
    + now apply Beta_AppR.
    + apply Sub_app2.

  - apply IH with (Lam u).
    + now apply Beta_Lam.
    + apply Sub_lam.

  (** Pairs and projections *)
  - apply IH with (Pair u t2).
    + now apply Beta_Pair1.
    + apply Sub_pair1.

  - apply IH with (Pair t1 u).
    + now apply Beta_Pair2.
    + apply Sub_pair2.

  - apply IH with (Pr1 u).
    + now apply Beta_Pr1.
    + apply Sub_pr1.

  - apply IH with (Pr2 u).
    + now apply Beta_Pr2.
    + apply Sub_pr2.

  (** Sum types *)
  - apply IH with (Pat u t2 t3).
    + now apply Beta_Pat1.
    + apply Sub_pat1.

  - apply IH with (Pat t1 u t3).
    + now apply Beta_Pat2.
    + apply Sub_pat2.

  - apply IH with (Pat t1 t2 u).
    + now apply Beta_Pat3.
    + apply Sub_pat3.

  - apply IH with (In1 u).
    + now apply Beta_In1.
    + apply Sub_in1.

  - apply IH with (In2 u).
    + now apply Beta_In2.
    + apply Sub_in2.
Qed.

Lemma SN_var_app (t: term) (n: var):
  SN (App t (Var n)) -> SN t.
Proof.
  intros ?.
  apply (SN_sub_term (App t (Var n))); [ assumption |].
  apply Sub_app1.
Qed.

Lemma SN_inverted (t: term):
  SN t -> forall (t': term), t ~> t' -> SN t'.
Proof.
  now inversion 1.
Qed.

Lemma reducible_is_SN (A : type):
  (forall (t: term), reducible A t -> SN t) /\
    (forall (t u: term), reducible A t -> t ~> u -> reducible A u) /\
    (forall (t: term), neutral t -> (forall (t': term), t ~> t' -> reducible A t') -> reducible A t).
Proof.
  induction A as [
    | A [IHA1 [IHA2 IHA3]] B [IHB1 [IHB2 IHB3]]
    | A [IHA1 [IHA2 IHA3]] B [IHB1 [IHB2 IHB3]]
    | A [IHA1 [IHA2 IHA3]] B [IHB1 [IHB2 IHB3]]].
  - do 3 split.
    + intros.
      apply SN_inverted with t'; [| assumption ].
      now apply SN_inverted with t.

    + intros.
      apply SN_inverted with u; [| assumption ].
      now apply SN_inverted with t.

    + assumption.

  - split; [| split ]; simpl.
    + intros ? Hred.
      apply Strong.

      intros ? ?.
      apply SN_inverted with t; [| assumption ].
      apply SN_var_app with 0.

      apply IHB1.
      apply Hred.
      apply IHA3; [ exact I |].
      inversion 1.

    + intros t ? IHred ? u Hred.
      apply IHB2 with (App t u).
      * apply IHred, Hred.
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
      apply IHA1 in Hred. apply SN_sub_term with (t' := t) in Hred.
      * assumption.
      * apply Sub_pr1.

    + intros t u [Hred1 Hred2] Hstep. split.
      * apply (IHA2 (Pr1 t) _ Hred1). now apply Beta_Pr1.
      * apply (IHB2 (Pr2 t) _ Hred2). now apply Beta_Pr2.

    + intros t Hneu H. split.
      * apply IHA3; [ exact I | ]. intros t' Hstep. inv Hstep; [| destruct Hneu ].
        apply (H s' H1).
      * apply IHB3; [ exact I | ]. intros t' Hstep. inv Hstep; [| destruct Hneu ].
        apply (H s' H1).

  - split; [| split]; simpl.
    + intros t [HSN _]. apply HSN.

    + intros t u [Hredt1 [Hredt2 Hredt3]] Hbeta. split; [| split].
      * apply (SN_inverted t Hredt1). assumption.
      * intros. apply Hredt2.
        apply rt_trans with u; [| assumption ].
        now apply rt_step.
      * intros. apply Hredt3.
        apply rt_trans with u; [| assumption ].
        now apply rt_step.

    + intros t Hneu H. split; [| split ].
      * apply Strong. intros t' ?. apply H. assumption.
      * intros u Hbeta. rewrite clos_rt_rt1n_iff in Hbeta.
        inv Hbeta; [ destruct Hneu |].
        apply H with y; [ assumption |]. apply clos_rt_rt1n_iff. assumption.
      * intros u Hbeta. rewrite clos_rt_rt1n_iff in Hbeta.
        inv Hbeta; [ destruct Hneu |].
        apply H with y; [ assumption |]. apply clos_rt_rt1n_iff. assumption.
Qed.

Lemma SN_subst (t: term) (σ: var -> term):
  SN t -> forall (u: term), t = u.[σ] -> SN u.
Proof.
  induction 1 as [? _ IHt]; intros; subst.

  apply Strong.
  intros t ?.

  apply IHt with t.[σ].
  - now apply beta_subst.
  - reflexivity.
Qed.

Lemma SN_ind_pair (P : term -> term -> Prop):
  (forall t u, (forall t' u', ((t = t' /\ u ~> u') \/ (t ~> t' /\ u = u')) -> P t' u') -> P t u)
    -> forall t u, SN t -> SN u -> P t u.
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

Lemma SN_triple_ind (P : term -> term -> term -> Prop):
  (forall t u v, (forall t' u' v',
                ((t = t' /\ u = u' /\ v ~> v') \/
                   (t = t' /\ u ~> u' /\ v = v') \/
                   (t ~> t' /\ u = u' /\ v = v'))
                -> P t' u' v') -> P t u v)
    -> forall t u v, SN t -> SN u -> SN v -> P t u v.
Proof.
  intros IH t u v Hsnt.
  revert u v.

  induction Hsnt as [? _ IHt].
  intros u v Hsnu. revert v.
  induction Hsnu as [? HSNu IHu].
  intros v Hsnv.
  induction Hsnv as [? HSNv IHv].
  apply IH.

  intros ? ? ? [[? [? ?]] | [[? [? ?]] | [? [? ?]]]]; subst.
  - now apply IHv.
  - apply IHu.
    + assumption.
    + apply Strong. intros. now apply HSNv.
  - apply IHt.
    + assumption.
    + apply Strong. intros. now apply HSNu.
    + apply Strong. intros. now apply HSNv.
Qed.

Lemma reducible_abs (v: term) (A B: type):
  (forall (u: term), reducible A u -> reducible B v.[u/]) -> reducible (Arr A B) (Lam v).
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

  inversion Hbeta; subst.
  - now apply Hred.

  - inversion H2; subst.
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
  intros. specialize (reducible_is_SN A) as (_ & _ & HA3).
  apply HA3.
  - exact I.
  - inversion 1.
Qed.

Lemma reducible_pair (A B: type) (u v: term):
  reducible A u ->
  reducible B v ->
  reducible (Prod A B) (Pair u v).
Proof.
  intros Hredu Hredv. simpl.
  specialize (reducible_is_SN A) as (HA1 & HA2 & HA3).
  specialize (reducible_is_SN B) as (HB1 & HB2 & HB3).
  assert (HSNu: SN u) by now apply HA1.
  assert (HSNv: SN v) by now apply HB1.
  revert Hredu Hredv.
  apply SN_ind_pair with (t := u) (u := v); [| assumption | assumption ].
  intros u' v' IH.
  intros Hredu' Hredv'. split.
  - apply HA3; [exact I |].
    intros t' Hred. inv Hred.
    + inv H0.
      * apply IH.
        -- now right.
        -- now apply HA2 with u'.
        -- assumption.
      * apply IH.
        -- now left.
        -- assumption.
        -- now apply HB2 with v'.
    + assumption.
  - apply HB3; [exact I |].
    intros t' Hred. inv Hred.
    + inv H0.
      * apply IH.
        -- now right.
        -- now apply HA2 with u'.
        -- assumption.
      * apply IH.
        -- now left.
        -- assumption.
        -- now apply HB2 with v'.
    + assumption.
Qed.

Lemma reducible_sum1 (A B: type) (s: term):
  reducible A s ->
  reducible (Sum A B) (In1 s).
Proof.
  intros Hreds. simpl.
  specialize (reducible_is_SN A) as (HA1 & HA2 & HA3).
  assert (HSN: SN s) by now apply HA1.
  induction HSN as [s _ IH]. split.
  - apply Strong. intros t' Hstep. inv Hstep. apply IH.
    + assumption.
    + now apply HA2 with s.
  - split.
    + intros u Hbeta; rewrite clos_rt_rt1n_iff in Hbeta;
      inv Hbeta; [ assumption |]. inv H.
      apply (IH s').
      * assumption.
      * now apply (HA2 s).
      * now apply clos_rt_rt1n_iff.
    + intros v Hbeta. rewrite clos_rt_rt1n_iff in Hbeta;
        inv Hbeta. inv H.
      apply (IH s').
      * assumption.
      * now apply (HA2 s).
      * now apply clos_rt_rt1n_iff.
Qed.

Lemma reducible_sum2 (A B: type) (s: term):
  reducible B s ->
  reducible (Sum A B) (In2 s).
Proof.
  intros Hreds. simpl.
  specialize (reducible_is_SN B) as (HB1 & HB2 & HB3).
  assert (HSN: SN s) by now apply HB1.
  induction HSN as [s _ IH]. split.
  - apply Strong. intros t' Hstep. inv Hstep. apply IH.
    + assumption.
    + now apply HB2 with s.
  - split.
    + intros u Hbeta; rewrite clos_rt_rt1n_iff in Hbeta;
      inv Hbeta. inv H.
      apply (IH s').
      * assumption.
      * now apply (HB2 s).
      * now apply clos_rt_rt1n_iff.
    + intros v Hbeta. rewrite clos_rt_rt1n_iff in Hbeta;
        inv Hbeta; [ assumption |]. inv H.
      apply (IH s').
      * assumption.
      * now apply (HB2 s).
      * now apply clos_rt_rt1n_iff.
Qed.

Lemma reducible_pat (A B C: type) (t u v: term):
  reducible (Sum A B) t ->
  reducible (Arr A C) (Lam u) ->
  reducible (Arr B C) (Lam v) ->
  reducible C (Pat t u v).
Proof.
  intros Hredt Hredu Hredv.
  specialize (reducible_is_SN (Arr A C)) as (HAC1 & HAC2 & HAC3).
  specialize (reducible_is_SN (Arr B C)) as (HBC1 & HBC2 & HBC3).
  specialize (reducible_is_SN (Sum A B)) as (H1 & H2 & H3).
  specialize (reducible_is_SN C) as (HC1 & HC2 & HC3).

  assert (HSNt: SN t) by now apply H1.
  assert (HSNu: SN u). {
    apply SN_sub_term with (Lam u).
    - apply HAC1. assumption.
    - apply Sub_lam.
  }

  assert (HSNv: SN v). {
    apply SN_sub_term with (Lam v).
    - apply HBC1. assumption.
    - apply Sub_lam.
  }

  revert Hredt Hredu Hredv. apply SN_triple_ind with (t := t) (u := u) (v := v).
  2, 3, 4: assumption.
  intros t0 u0 v0 IH Hredt0 Hredu0 Hredv0. apply HC3; [ exact I |].
  intros t' Hstep. inv Hstep.
  - apply IH; try assumption.
    + right. now right.
    + apply H2 with t0; assumption.
  - apply IH; try assumption.
    + right. now left.
    + apply HAC2 with (Lam u0); [ assumption | now apply Beta_Lam ].
  - apply IH; try assumption.
    + now left.
    + apply HBC2 with (Lam v0); [ assumption | now apply Beta_Lam ].
  - enough (reducible C (App (Lam u0) t1)).
    + apply HC2 with (App (Lam u0) t1).
      * assumption.
      * now apply Beta_Subst.
    + simpl in Hredu0. apply Hredu0. apply Hredt0. apply rt_refl.
  - enough (reducible C (App (Lam v0) t1)).
    + apply HC2 with (App (Lam v0) t1).
      * assumption.
      * now apply Beta_Subst.
    + simpl in Hredv0. apply Hredv0. apply Hredt0. apply rt_refl.
Qed.

Lemma typing_is_reducible (Γ: var -> type) (σ: var -> term):
  (forall (x: var), reducible (Γ x) (σ x)) ->
    forall (A: type) (t: term), Γ ⊢ t : A -> reducible A t.[σ].
Proof.
  intros Hred A t.
  revert Hred.
  revert σ A Γ.

  induction t; intros σ A Γ Hred.
  all: inversion 1; subst.

  - apply Hred.
  - apply IHt1 with (σ := σ) in H2; [| assumption ].
    apply IHt2 with (σ := σ) in H4; [| assumption ].
    now apply H2.
  - apply reducible_abs.
    intros u Hredu. asimpl.
    apply IHt with (A0 .: Γ); [| assumption ].
    intros [| x ]; simpl; [ assumption |].
    apply Hred.

  - apply reducible_pair.
    + now eapply IHt1.
    + now eapply IHt2.

  - apply (IHt σ (Prod A B) Γ Hred H1).
  - apply (IHt σ (Prod A0 A) Γ Hred H1).

  - simpl. apply reducible_pat with A0 B.
    + now apply IHt with Γ.
    + apply reducible_abs. intros u0 Hredu0.
      asimpl. apply IHt0 with (A0 .: Γ); [| assumption ].
      intros [| x ]; simpl; [ assumption | apply Hred ].
    + apply reducible_abs. intros. asimpl. apply IHt1 with (B .: Γ); [| assumption ].
      intros [| x ]; simpl; [ assumption | apply Hred ].
  - change (reducible (Sum A0 B) (In1 t.[σ])).
    apply reducible_sum1. now apply IHt with Γ.
  - change (reducible (Sum A0 B) (In2 t.[σ])).
    apply reducible_sum2. now apply IHt with Γ.
Qed.

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
