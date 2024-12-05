From FormArith.SimplyTypedLambdaCalculus Require Import Definitions.
From Coq Require Import  Lia .

Inductive SN: term -> Prop :=
  | Strong (t: term) :
      (forall (t': term), t ~> t' -> SN t') -> SN t.

Fixpoint reducible (A: type) (t: term): Prop :=
  match A with
  | Base | Nat => SN t
  | Arr A B => forall (u: term), reducible A u -> reducible B (App t u)
  end.

Definition neutral (t: term): Prop :=
  match t with
  | Lam _ | Const_0 | Const_S _ => False
  | _ => True
  end.

Inductive sub_term: term -> term -> Prop :=
  | Sub_app1 (t1 t2: term) : sub_term t1 (App t1 t2)
  | Sub_app2 (t1 t2: term) : sub_term t2 (App t1 t2)
  | Sub_lam (t: term) : sub_term t (Lam t)
  | Sub_S (s : term) : sub_term s (Const_S s)
  | Sub_R0 (t0 ts n: term) : sub_term t0 (Rec t0 ts n)
  | Sub_RS (t0 ts n: term) : sub_term ts (Rec t0 ts n).

Lemma SN_lam (t: term):
  SN t -> SN (Lam t).
Proof.
  revert t.

  apply SN_ind; intros ? _ H.
  apply Strong; intros ? Hbeta.
  inversion Hbeta; subst.
  now apply H.
Qed.

Lemma SN_S (t: term):
  SN t -> SN (Const_S t).
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

  (* case: Sub_app1 *)
  - apply IH with (App u t2).
    + now apply Beta_AppL.
    + apply Sub_app1.

  (* case: Sub_app2 *)
  - apply IH with (App t1 u).
    + now apply Beta_AppR.
    + apply Sub_app2.

  (* case: Sub_lam *)
  - apply IH with (Lam u).
    + now apply Beta_Lam.
    + apply Sub_lam.

  (* case: Sub_S *)
  - apply IH with (Const_S u).
    + now apply Beta_S.
    + apply Sub_S.

  (* case: Sub_R0 *)
  - apply IH with (Rec u ts n).
    + now apply Beta_RI0.
    + apply Sub_R0.

  (* case: Sub_R0 *)
  - apply IH with (Rec t0 u n).
    + now apply Beta_RIS.
    + apply Sub_RS.

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
  induction A as [ | | A [IHA1 [IHA2 IHA3]] B [IHB1 [IHB2 IHB3]] ].
  - do 3 split.
    + intros.
      apply SN_inverted with t'; [| assumption ].
      now apply SN_inverted with t.

    + intros.
      apply SN_inverted with u; [| assumption ].
      now apply SN_inverted with t.

    + assumption.

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
Qed.

Lemma reducible_CR1 (A : type) (t: term): reducible A t -> SN t.
Proof.
apply reducible_is_SN.
Qed.

Lemma reducible_CR2 (A : type) (t u: term): reducible A t -> t ~> u -> reducible A u.
Proof.
apply reducible_is_SN.
Qed.

Lemma reducible_CR3 (A: type) (t: term):
  neutral t -> (forall (t': term), t ~> t' -> reducible A t') -> reducible A t.
Proof.
apply reducible_is_SN.
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
  (forall t u,
    (forall t' u', ((t = t' /\ u ~> u') \/ (t ~> t' /\ u = u'))
                   -> P t' u')
    -> P t u)
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
    (forall s t u,
      (forall s', s ~> s' -> P s' t u)
      -> (forall t', t ~> t' -> P s t' u)
      -> (forall u', u ~> u' -> P s t u') -> P s t u)
    -> forall s t u, SN s -> SN t -> SN u -> P s t u.
Proof.
  intros IH s t u Hs.
  revert t u. induction Hs as [s Hs1 Hs2].
  apply Strong in Hs1.
  intros t u Ht.
  revert u. induction Ht as [t Ht1 Ht2].
  apply Strong in Ht1.
  intros u Hu. induction Hu as [u Hu1 Hu2].
  apply Strong in Hu1.
  apply IH.
  - intros. apply Hs2. all: assumption.
  - intros. apply Ht2. all: assumption.
  - intros. apply Hu2. all: assumption.
Qed.

Lemma reducible_Rec (t0 ts n : term) (A: type):
  reducible A t0 
  -> reducible (Arr Nat (Arr A A)) ts
  -> reducible Nat n
  -> reducible A (Rec t0 ts n).
Proof.
intros Hrt0 Hrts Hrn.
apply reducible_CR1 in Hrt0 as Hsnt0.
apply reducible_CR1 in Hrts as Hsnts.
apply reducible_CR1 in Hrn as Hsnn.
revert Hrn Hrts Hrt0.
apply SN_triple_ind with (s := t0) (t := ts) (u := n); [ | assumption .. ].
clear Hsnt0 Hsnts Hsnn.
clear t0 ts n.
intros t0 ts n Ht0' Hts' Hn' Hn Hts Ht0.
apply reducible_CR3; [now simpl |].
inversion 1; subst.
  - assumption.
  - simpl in Hts. apply Hts.
    ** apply SN_sub_term with (t := Const_S n0); [apply Hn | constructor].
    ** admit.
  - apply Ht0'. all: try assumption.
    apply reducible_CR2 with (t := t0). all: assumption.
  - apply Hts'. all: try assumption.
    apply reducible_CR2 with (t := ts). all: assumption.
Admitted.

Lemma reducible_abs (v: term) (A B: type):
  (forall (u: term), reducible A u -> reducible B v.[u/]) 
  -> reducible (Arr A B) (Lam v).
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
  intros.
  destruct A.
  - simpl. apply Strong. inversion 1.
  - simpl. apply Strong. inversion 1.
  - apply reducible_is_SN; [ exact I |].
    inversion 1.
Qed.

Lemma size_recursion (X : Type) (sigma : X -> nat) (p : X -> Type) :
  (forall x, (forall y, sigma y < sigma x -> p y) -> p x) ->
  forall x, p x.
Proof.
  intros D x. apply D.
  cut (forall n y, sigma y < n -> p y); [now eauto |].
  clear x. intros n.
  induction n; intros y E.
  - exfalso. inversion E.
  - apply D. intros x F. apply IHn. lia.
Defined.


Lemma typing_is_reducible (Γ: var -> type) (σ: var -> term):
  (forall (x: var), reducible (Γ x) (σ x)) ->
    forall (A: type) (t: term), Γ ⊢ t : A -> reducible A t.[σ].
Proof.
  intros Hred A t.
  revert Hred.
  revert σ A Γ.

  induction t; intros σ A Γ Hred.
  all: inversion 1; subst; simpl.

  - apply Hred.

  - apply IHt1 with (σ := σ) in H2; [| assumption ].
    apply IHt2 with (σ := σ) in H4; [| assumption ].
    now apply H2.

  - apply reducible_abs.
    intros u Hredu. asimpl.
    apply IHt with (A0 .: Γ); [| assumption ].
    intros [| x ]; simpl; [ assumption |].
    apply Hred.

  (* case: Const_0 *)
  - apply Strong. inversion 1.

  (* case: Const_S *)
  - specialize (IHt σ Nat Γ Hred H1).
    simpl in IHt.
    now apply SN_S.

  (* case: Rec *)
  - specialize (IHt1 σ A Γ Hred H3).
    specialize (IHt2 σ (Arr Nat (Arr A A)) Γ Hred H5).
    specialize (IHt3 σ Nat Γ Hred H6).
    apply reducible_Rec. all: assumption.
Qed.

Corollary ST_is_SN (A: type) (Γ: var -> type) (t: term):
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
