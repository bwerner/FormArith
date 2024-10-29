From FormArith.SimplyTypedLambdaCalculus Require Import Definitions.


Inductive SN: term -> Prop :=
  | Strong (t: term) :
      (forall (t': term), step t t' -> SN t') -> SN t.

Fixpoint reducible (A: type) (t: term): Prop :=
  match A with
  | Base => SN t
  | Arr A B => forall (u: term), reducible A u -> reducible B (App t u)
  end.

Definition neutral (t: term): Prop :=
  match t with
  | Lam _ => False
  | _ => True
  end.

Inductive sub_term: term -> term -> Prop :=
  | Sub_app1 (t1 t2: term) : sub_term t1 (App t1 t2)
  | Sub_app2 (t1 t2: term) : sub_term t2 (App t1 t2)
  | Sub_lam (t: term) : sub_term t (Lam t).


Lemma SN_lam (t: term):
  SN t -> SN (Lam t).
Proof.
  revert t.

  apply SN_ind; intros ? _ H.
  apply Strong; intros ? Hstep.
  inversion Hstep; subst.
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

  - apply IH with (App u t2).
    + now apply Step_app1.
    + apply Sub_app1.

  - apply IH with (App t1 u).
    + now apply Step_app2.
    + apply Sub_app2.

  - apply IH with (Lam u).
    + now apply Step_lam.
    + apply Sub_lam.
Qed.

Lemma SN_var_app (t: term) (n: var):
  SN (App t (Var n)) -> SN t.
Proof.
  intros ?.
  apply (SN_sub_term (App t (Var n))); [ assumption |].
  apply Sub_app1.
Qed.

Lemma SN_inverted (t: term):
  SN t -> forall (t': term), step t t' -> SN t'.
Proof.
  now inversion 1.
Qed.

Lemma reducible_is_SN (A : type):
  (forall (t: term), reducible A t -> SN t) /\
    (forall (t u: term), reducible A t -> step t u -> reducible A u) /\
    (forall (t: term), neutral t -> (forall (t': term), step t t' -> reducible A t') -> reducible A t).
Proof.
  induction A as [ | A [IHA1 [IHA2 IHA3]] B [IHB1 [IHB2 IHB3]] ].
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
      * now apply Step_app1.

    + intros ? ? Hredt ? Hredu.
      apply IHA1 in Hredu as HSNu.
      induction HSNu as [ u _ IHu ].

      apply IHB3; [ exact I |].
      inversion 1; subst.
      * contradiction.
      * now apply Hredt.
      * apply IHu; [ assumption |].
        now apply IHA2 with u.
Qed.

Lemma SN_subst (t: term) (sigma: var -> term):
  SN t -> forall (u: term), t = u.[sigma] -> SN u.
Proof.
  induction 1 as [? _ IHt]; intros; subst.

  apply Strong.
  intros t ?.

  apply IHt with t.[sigma].
  - now apply step_subst.
  - reflexivity.
Qed.

Lemma SN_ind_pair (P : term -> term -> Prop):
  (forall t u, (forall t' u', ((t = t' /\ step u u') \/ (step t t' /\ u = u')) -> P t' u') -> P t u)
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
  intros t Hstep.

  inversion Hstep; subst.
  - now apply Hred.

  - inversion H2; subst.
    apply IH; [ .. | assumption ].
    { now right. }

    intros.
    apply HB2 with x.[u0/].
    + now apply Hred.
    + now apply step_subst.

  - apply IH.
    + now left.
    + now apply Hred.
    + now apply HA2 with y.
Qed.


Lemma reducible_var (A: type) (x: var) (gamma: var -> type):
  types gamma (Var x) A -> reducible A (Var x).
Proof.
  intros.
  destruct A.
  - simpl.
    apply Strong.
    inversion 1.
  - apply reducible_is_SN; [ exact I |].
    inversion 1.
Qed.

Lemma typing_is_reducible (gamma: var -> type) (sigma: var -> term):
  (forall (x: var), reducible (gamma x) (sigma x)) ->
    forall (A: type) (t: term), types gamma t A -> reducible A t.[sigma].
Proof.
  intros Hred A t.
  revert Hred.
  revert sigma A gamma.

  induction t; intros sigma A gamma Hred.
  all: inversion 1; subst; simpl.

  - apply Hred.
  - apply IHt1 with (sigma := sigma) in H2; [| assumption ].
    apply IHt2 with (sigma := sigma) in H4; [| assumption ].
    now apply H2.
  - apply reducible_abs.
    intros u Hredu. asimpl.
    apply IHt with (A0 .: gamma); [| assumption ].
    intros [| x ]; simpl; [ assumption |].
    apply Hred.
Qed.

Corollary STLC_is_SN (A: type) (gamma: var -> type) (t: term):
  types gamma t A -> SN t.
Proof.
  intros.
  apply (reducible_is_SN A).
  replace t with t.[ids] by apply subst_id.
  apply typing_is_reducible with gamma; [| assumption ].
  intros.
  apply reducible_var with gamma.
  now apply Types_var.
Qed.
