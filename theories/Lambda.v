From Autosubst Require Import Autosubst.

Check subst_comp.

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
  intros x sigma. simpl. reflexivity.
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
  - inversion Hstep.
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

Lemma type_subst :
  forall (Gamma Delta : var -> type) (s : term) (A : type) (sigma : var -> term),
    types Gamma s A ->
    (forall (x:var) , types Delta (sigma x) (Gamma x)) ->
    types Delta s.[sigma] A.
Proof.
  intros Gamma Delta s. revert Gamma Delta. induction s; intros; simpl.
  - inversion H. subst. apply H0.
  - inversion H. subst. eapply Types_app.
    + eapply IHs1.
      * apply H3.
      * assumption.
    + eapply IHs2; eassumption.
  - inversion H. subst. constructor. eapply IHs.
    + eassumption.
    + intros x. destruct x.
      * constructor. reflexivity.
      * asimpl. eapply type_weakening.
        -- apply H0.
        -- asimpl. reflexivity.
Qed.

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
      * intros [|x]; asimpl; auto. constructor. reflexivity.
    + inversion H. subst. econstructor.
      * apply IHs1; eassumption.
      * assumption.
    + inversion H. subst. econstructor.
      * eassumption.
      * apply IHs2; assumption.
  - inversion H0. subst. inversion H. subst.
    constructor. apply IHs; assumption.
Qed.

(** STRONG NORMALISATION PROOF *)

Inductive sn : term -> Prop :=
| Strong (t : term) :
  (forall (t' : term), step t t' -> sn t') -> sn t.

Example sn_var : forall (n : var), sn (Var n).
Proof.
  constructor. intros. inversion H.
Qed.

Fixpoint reducible (A : type) (t : term) : Prop :=
  match A with
  | Base => sn t
  | Arr A B => forall (u : term), reducible A u -> reducible B (App t u)
  end.

Definition neutral (t : term) : Prop :=
  match t with
  | Lam _ => False
  | _ => True
  end.

Lemma sn_app_var : forall (t : term) (n : var), sn (App t (Var n)) -> sn t.
Proof.
  intros t n Hsn. Check sn_ind.

Lemma reducible_is_sn :
  forall (A : type),
  (forall (t : term), reducible A t -> sn t)  /\
    (forall (t u : term), reducible A t -> step t u -> reducible A u) /\
    (forall (t : term), neutral t -> (forall t':term, step t t' -> reducible A t') -> reducible A t).
Proof.
  induction A as [| A [IHA1 [IHA2 IHA3]] B [IHB1 [IHB2 IHB3]]].
  - split; split.
    + simpl in H. inversion H. assumption.
    + simpl. intros t u H Hstep. inversion H. subst. auto.
    + simpl. intros t _ H. constructor. assumption.
  - split; split.
    + assert (E0 : reducible A (Var 0)). {
        apply IHA3.
        * simpl. auto.
        * intros. inversion H0.
      }
      simpl in H. apply H in E0. apply IHB1 in E0.
