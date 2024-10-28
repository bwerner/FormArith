From FormArith Require Export Base.

From Autosubst Require Import Autosubst.

Inductive term : Type :=
| Var (n : var)
| App (s t : term)
| Lam (s : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term.  derive. Defined.
Instance Subst_term : Subst term. derive. Defined.

Instance SubstLemmas_term : SubstLemmas term. derive. Defined.

Lemma var_subst:
  forall (x:var) (sigma : var -> term), (Var x).[sigma] = sigma x.
Proof.
  now intros x sigma.
Qed.

Inductive step : term -> term -> Prop :=
| Step_beta (s s' t : term) : s' = s.[t .: ids] -> step (App (Lam s) t) s'
| Step_app1 (s s' t : term) : step s s' -> step (App s t) (App s' t)
| Step_app2 (s t t' : term) : step t t' -> step (App s t) (App s t')
| Step_lam (s s' : term) : step s s' -> step (Lam s) (Lam s').

Lemma step_subst :
  forall (t t' : term) (sigma : var -> term),
    step t t' -> step t.[sigma] t'.[sigma].
Proof.
  induction t; intros t' sigma Hstep.
  - easy.
  - inversion Hstep; subst.
    + simpl. constructor. asimpl. reflexivity.
    + simpl. constructor. auto.
    + simpl. constructor. auto.
  - inversion Hstep. subst. simpl.
    constructor. auto.
Qed.

Inductive type :=
| Base
| Arr (A B : type).

Inductive types (Gamma : var -> type) : term -> type -> Prop :=
| Types_var (x : var) (A : type) : Gamma x = A -> types Gamma (Var x) A
| Types_app (s t : term) (A B : type) :
  types Gamma s (Arr A B) -> types Gamma t A ->
  types Gamma (App s t) B
| Types_lam (s : term) (A B : type) : types (A .: Gamma) s B -> types Gamma (Lam s) (Arr A B).

Lemma type_weakening :
  forall (Gamma : var -> type) (s : term) (A : type),
    types Gamma s A ->
    (forall Delta xi, Gamma = xi >>> Delta -> types Delta s.[ren xi] A).
Proof.
  intros Gamma s A H. induction H; intros; simpl; econstructor; auto.
  - rewrite H0 in H. auto.
  - asimpl. apply IHtypes. rewrite H0. asimpl. reflexivity.
Qed.

Create HintDb typingSTLC.

Hint Resolve type_weakening : typingSTLC.
Hint Resolve Types_app : typingSTLC.
Hint Resolve Types_var : typingSTLC.



#[export] Hint Extern 3 (@types _ _ _) => asimpl : typingSTLC.



Lemma type_subst :
  forall (Gamma Delta : var -> type) (s : term) (A : type) (sigma : var -> term),
    types Gamma s A ->
    (forall (x:var) , types Delta (sigma x) (Gamma x)) ->
    types Delta s.[sigma] A.
Proof.
  intros Gamma Delta s. revert Gamma Delta. induction s; intros; simpl; inversion H; subst.
  - auto.
  - eauto with typingSTLC.
  - constructor. eapply IHs.
    + eassumption.
    + intros [| x]; eauto with typingSTLC.
Qed.

Hint Resolve type_subst : typingSTLC.

Lemma type_pres :
  forall (Gamma : var -> type) (s t : term) (A : type),
    types Gamma s A -> step s t -> types Gamma t A.
Proof.
  intros Gamma s. revert Gamma. induction s; intros; asimpl; auto.
  - inversion H0.
  - inversion H0; subst.
    + inversion H; subst. inversion H3; subst.
      eapply type_subst.
      * eassumption.
      * intros [|x]; eauto with typingSTLC.
    + inversion H. subst. eauto 3 with typingSTLC.
    + inversion H. subst. eauto 3 with typingSTLC.
  - inversion H0. subst. inversion H. subst.
    constructor. apply IHs; assumption.
Qed.

(** STRONG NORMALISATION PROOF *)

Inductive sn : term -> Prop :=
| Strong (t : term) :
  (forall (t' : term), step t t' -> sn t') -> sn t.

Example sn_var : forall (n : var), sn (Var n).
Proof.
  now constructor.
Qed.

Fixpoint reducible (A : type) (t : term) : Prop :=
  match A with
  | Base => sn t
  | Arr A B => forall (u : term), reducible A u -> reducible B (App t u)
  end.


#[export] Hint Extern 3 (reducible _ _) => asimpl : typingSTLC.


Definition neutral (t : term) : Prop :=
  match t with
  | Lam _ => False
  | _ => True
  end.

Lemma sn_lam : forall (t : term),
    sn t -> sn (Lam t).
Proof.
  apply sn_ind.
  intros. constructor.
  intros t' Hstep.
  inversion Hstep.
  auto.
Qed.

Inductive sub_term : term -> term -> Prop :=
| Sub_app1 (t1 t2 : term) : sub_term t1 (App t1 t2)
| Sub_app2 (t1 t2 : term) : sub_term t2 (App t1 t2)
| Sub_lam (t : term) : sub_term t (Lam t).

Lemma sn_sub_term : forall (t : term),
    sn t -> (forall t':term, sub_term t' t -> sn t').
Proof.
  intros t H. induction H.
  intros t' Hsub. inversion Hsub; subst; constructor.
  - intros u Hstep.
    eapply H0; constructor; easy.
  - eauto using Sub_app2, Step_app2.
  - eauto using Sub_lam, Step_lam.
Qed.

Corollary sn_var_app : forall (t : term) (n :var), sn (App t (Var n)) -> sn t.
Proof.
  intros t n H. apply (sn_sub_term (App t (Var n))).
  - assumption.
  - constructor.
Qed.

Lemma sn_inverted : forall t, sn t -> forall t', step t t' -> sn t'.
Proof.
  intros t h.
  now inversion h.
Qed.

Lemma reducible_is_sn :
  forall (A : type),
  (forall (t : term), reducible A t -> sn t)  /\
    (forall (t u : term), reducible A t -> step t u -> reducible A u) /\
    (forall (t : term), neutral t -> (forall t':term, step t t' -> reducible A t') -> reducible A t).
Proof.
  induction A as [| A [IHA1 [IHA2 IHA3]] B [IHB1 [IHB2 IHB3]]].
  - split; split; simpl.
    + eauto using sn_inverted.
    + eauto using sn_inverted.
    + now constructor.
  - split; split.
    + assert (E0 : reducible A (Var 0)). { now apply IHA3. }
      eauto using sn_var_app, sn_inverted.
    + simpl. eauto using Step_app1.
    + simpl. intros t Hneu Hredt u Hredu.
      apply IHA1 in Hredu as Hsnu. induction Hsnu as [u _ IHu].
      assert (E : forall v:term, step (App t u) v -> reducible B v). {
        intros v Hstep. inversion Hstep; subst; now eauto.
      }
      now apply IHB3.
Qed.


Lemma sn_subst : forall (t : term) (sigma : var -> term),
    sn t -> (forall u:term, t = u.[sigma] -> sn u).
Proof.
  intros t sigma Hsn. induction Hsn as [t _ IHt].
  intros u ->. eauto using step_subst, Strong.
Qed.

Lemma sn_ind_pair :
  forall (P : term -> term -> Prop),
    (forall t u, (forall t' u', ((t = t' /\ step u u') \/ (step t t' /\ u = u')) -> P t' u') -> P t u) ->
    forall t u, sn t -> sn u -> P t u.
Proof.
  intros P IH t u Hsnt.
  revert u.
  induction Hsnt as [t _ IHt].
  intros v Hsnv. induction Hsnv as [v Hsnv IHv].
  apply IH. intros t' v' [[H1 H2] | [H1 H2]]; subst; auto using Strong.
Qed.



Lemma reducible_abs :
  forall (v : term) (A B : type),
    (forall (u:term), reducible A u -> reducible B v.[u/]) -> reducible (Arr A B) (Lam v).
Proof.
  intros v A B H u Hredu.
  specialize (reducible_is_sn A) as [HA1 [HA2 HA3]].
  specialize (reducible_is_sn B) as [HB1 [HB2 HB3]].
  apply HA1 in Hredu as Hsnu.
  assert (Hsnv : sn v). {
    apply H in Hredu. apply HB1 in Hredu. apply sn_subst with (t := v.[u/]) (sigma := u .: ids); auto.
  }
  revert H Hredu. apply sn_ind_pair with (t := v) (u := u).
  - intros x y IH H Hred. apply HB3. { split. }
    intros t Hstep. inversion Hstep; subst.
    + apply H. apply Hred.
    + inversion H3. subst. eauto 7 using step_subst.
    + eauto.
  - apply Hsnv.
  - apply Hsnu.
Qed.

Hint Resolve reducible_abs : typingSTLC.

Lemma reducible_var : forall x A Gamma, types Gamma (Var x) A -> reducible A (Var x).
Proof.
  intros x A Gamma wt.
  destruct A.
  - apply sn_var.
  - now apply reducible_is_sn.
Qed.

Hint Resolve reducible_var : typingSTLC.

Lemma typing_is_reducible :
  forall (Gamma : var -> type) (sigma : var -> term),
    (forall (x:var), reducible (Gamma x) (sigma x)) ->
    forall (A:type) (t:term), types Gamma t A -> reducible A t.[sigma].
Proof.
  intros Gamma sigma adapted A t.
  generalize dependent Gamma.
  generalize dependent A.
  generalize dependent sigma.
  induction t; intros sigma A Gamma adapted wellTyped; simpl; inversion wellTyped; subst.
  - apply adapted.
  - apply IHt1 with (sigma := sigma) in H1; auto.
    apply IHt2 with (sigma := sigma) in H3; auto.
  - apply reducible_abs.
    intros u Hredu. asimpl.
    eapply IHt; eauto.
    intros [| x]; simpl; auto.
Qed.

Corollary STLC_is_SN : forall Gamma A t, types Gamma t A -> sn t.
Proof.
  intros Gamma A t wellTyped.
  apply (reducible_is_sn A).
  specialize (typing_is_reducible Gamma ids).
  intro H.
  asimpl in H.
  eauto with typingSTLC.
Qed.
