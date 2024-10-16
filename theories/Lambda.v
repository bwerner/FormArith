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

Lemma sn_lam : forall (t : term),
    sn t -> sn (Lam t).
Proof.
  apply sn_ind.
  intros. constructor.
  intros t' Hstep.
  inversion Hstep. subst. apply H0. assumption.
Qed.

Inductive sub_term : term -> term -> Prop :=
| Sub_app1 (t1 t2 : term) : sub_term t1 (App t1 t2)
| Sub_app2 (t1 t2 : term) : sub_term t2 (App t1 t2)
| Sub_lam (t : term) : sub_term t (Lam t).

Lemma sn_sub_term : forall (t : term),
    sn t -> (forall t':term, sub_term t' t -> sn t').
Proof.
  intros t H. induction H.
  intros t' Hsub. inversion Hsub; subst.
  - constructor. intros u Hstep.
    eapply H0.
    + constructor. apply Hstep.
    + constructor.
  - constructor. intros u Hstep. eapply H0.
    + apply Step_app2. apply Hstep.
    + constructor.
  - constructor. intros u Hstep. eapply H0.
    + constructor. apply Hstep.
    + constructor.
Qed.

Corollary sn_var_app : forall (t : term) (n :var), sn (App t (Var n)) -> sn t.
Proof.
  intros t n H. apply (sn_sub_term (App t (Var n))).
  - assumption.
  - constructor.
Qed.

Check sn_ind.


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
      apply sn_var_app in E0.
      inversion E0.
      subst.
      assumption.
   + intros t t' Hredt Hstep.
     intros u Hredu.
     apply IHB2 with (App t u).
     * apply Hredt.
       assumption.
     * constructor. assumption.
   + simpl. intros t Hneu Hredt u Hredu.
     apply IHA1 in Hredu as Hsnu. induction Hsnu as [u _ IHu].
     assert (E : forall v:term, step (App t u) v -> reducible B v). {
       intros v Hstep. inversion Hstep; subst.
       * destruct Hneu.
       * apply Hredt; assumption.
       * apply (IHu t').
         -- assumption.
         -- apply (IHA2 u); assumption. }
     apply IHB3.
     * split.
     * apply E.
Qed.


Lemma sn_subst : forall (t : term) (sigma : var -> term),
    sn t -> (forall u:term, t = u.[sigma] -> sn u).
Proof.
  intros t sigma Hsn. induction Hsn as [t _ IHt].
  intros u Hsubst. constructor.
  intros v Hstep. specialize (IHt v.[sigma]). apply IHt; auto.
  rewrite Hsubst. apply step_subst. assumption.
Qed.


Lemma typing_is_reducible :
  forall (Gamma : var -> type) (sigma : var -> term),
    (forall (x:var), reducible (Gamma x) (sigma x)) ->
    forall (A:type) (t:term), types Gamma t A -> reducible A t.[sigma].
Proof.
  intros Gamma sigma adapted A t.
  generalize dependent Gamma.
  generalize dependent A.
  generalize dependent sigma.
  induction t; intros sigma A Gamma adapted wellTyped.
  - simpl.
    inversion wellTyped.
    subst.
    apply adapted.
  - simpl.
    inversion wellTyped.
    subst.
    rename A0 into B.
    apply IHt1 with (sigma := sigma) in H1; try assumption.
    apply IHt2 with (sigma := sigma) in H3; try assumption.
    simpl in H1.
    apply H1.
    apply H3.
  - simpl.
    inversion wellTyped.
    subst.
    rename A0 into A. simpl.
    intros u Hredu. specialize (reducible_is_sn B). intros [ Hsn [ Hstable Hred ]].
    apply Hred. { split. }
    apply IHt with (sigma := up sigma) in H0 as Hreds.
    + specialize (reducible_is_sn A) as [ HsnA _]. apply HsnA in Hredu as Hsnu. clear HsnA.
      apply Hsn in Hreds as Hsns.
      induction Hsnu as [u _ IHu]. eapply sn_subst in Hsns as Hsns'; auto.
      induction Hsns' as [s _ IHs].
      intros v Hstep. inversion Hstep; subst.
      * asimpl. apply IHt with (Gamma := A .: Gamma); auto.
        intros [| x]; simpl. apply Hredu. apply adapted.
      * admit. (* STUCK AHHHHHHH*)

(*
    specialize (IHt (up sigma)).
    *)
    
    
    
    
  Admitted.
