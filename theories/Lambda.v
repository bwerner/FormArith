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
  forall (Gamma : var -> type) (s : term) (A : type) (sigma : var -> term),
    types Gamma s A ->
    (forall (x:var) (B:type) , Gamma x = B -> types Gamma (sigma x) B) ->
    types Gamma s.[sigma] A.
Proof.
  intros Gamma s. revert Gamma. induction s; intros; simpl.
  - apply H0. inversion H. subst. reflexivity.
  - inversion H. subst. eapply Types_app.
    + apply IHs1.
      * apply H3.
      * assumption.
    + apply IHs2; assumption.
  - inversion H. subst. constructor. apply IHs.
    + assumption.
    + intros. destruct x.
      * simpl in H1. subst. constructor. reflexivity.
      * simpl in H1. apply H0 in H1 as E. asimpl.
        eapply type_weakening.
        -- apply E.
        -- asimpl. reflexivity.
Qed.

Lemma type_pres :
  forall (Gamma : var -> type) (s t : term) (A : type),
    types Gamma s A -> step s t -> types Gamma t A.
Proof.
  intros Gamma s t A Hty Hstep. induction Hstep.
  - inversion Hty. inversion H2. subst. Abort.
       (* substitution lemma not strong enough *)
