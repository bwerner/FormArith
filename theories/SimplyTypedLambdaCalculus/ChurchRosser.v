From FormArith.SimplyTypedLambdaCalculus Require Import Definitions.

Require Import Relations.Relations.

Reserved Notation "t >=> t'" (at level 60).

(** Parallel reduction *)
Inductive par_red: term -> term -> Prop :=
  | ParRed_Subst (s s' t t': term):
    s >=> s' ->
    t >=> t' ->
    App (Lam s) t >=> s'.[t'/]

  | ParRed_Var (v: var): (Var v) >=> (Var v)
    
  | ParRed_App (s s' t t': term) :
    s >=> s' ->
    t >=> t' ->
    App s t >=> App s' t'
    
  | ParRed_Lam (t t': term) :
    t >=> t' ->
    Lam t >=> Lam t'
  where "t >=> t'" := (par_red t t').

Notation "R *" := (clos_refl_trans _ R)
  (at level 8, no associativity, format "R *").
Notation "t ~>* t'" := (beta* t t') (at level 70, t' at next level).
Notation "t >=>* t'" := (par_red* t t') (at level 70, t' at next level).

Definition local_confluence (P: term -> term -> Prop): Prop :=
  forall (t u v: term),
  P t u ->
  P t v ->
  exists (w : term), P u w /\ P v w.

Definition CR (P: term -> term -> Prop) :=
  local_confluence (clos_refl_trans _ P).

Fixpoint par_red_max_reduction (t: term): term :=
  match t with
  | Var v => Var v
  | App (Lam t) u => (par_red_max_reduction t).[(par_red_max_reduction u)/]
  | App t u => App (par_red_max_reduction t) (par_red_max_reduction u)
  | Lam t => Lam (par_red_max_reduction t)
  end.

Definition replace_lambda (f: term -> term) (s u: term): term :=
  match s with
  | Lam s' => f s'
  | _ => u
  end.


Lemma par_red_refl (t: term):
  t >=> t.
Proof.
  induction t.
  - apply ParRed_Var.
  - apply ParRed_App; assumption.
  - apply ParRed_Lam.
    assumption.
Qed.

Lemma beta_star_refl (t: term):
  t ~>* t.
Proof.
  apply rt_refl.
Qed.

Lemma beta_star_trans (x y z: term):
  x ~>* y -> y ~>* z -> x ~>* z.
Proof.
  intros Hxy Hyz.
  apply rt_trans with (y := y); assumption.
Qed.

Lemma par_red_app_l (s s' t: term) :
  s ~>* s' -> App s t ~>* App s' t.
Proof.
  intros Hs.
  induction Hs as [ ? ? ? | ? | x y z ? ? ? ? ].
  - apply rt_step.
    apply Beta_AppL.
    assumption.
  - apply rt_refl.
  - apply rt_trans with (y := App y t); assumption.
Qed.

Lemma par_red_app_r (s t t': term) :
  t ~>* t' -> App s t ~>* App s t'.
Proof.
  intros Hs.
  induction Hs as [ ? ? ? | ? | x y z ? ? ? ? ].
  - apply rt_step.
    apply Beta_AppR.
    assumption.
  - apply rt_refl.
  - apply rt_trans with (y := App s y); assumption.
Qed.

Lemma beta_to_par_red : forall (s t : term),
  s ~> t -> s >=> t.
Proof.
  intros s t H.
  induction H.
  - rewrite H.
    apply ParRed_Subst; apply par_red_refl.
  - apply ParRed_App; [ assumption | apply par_red_refl ].
  - apply ParRed_App; [ apply par_red_refl | assumption ].
  - apply ParRed_Lam.
    assumption.
Qed.

Lemma par_red_subst (t t': term) (sigma: var -> term):
  t >=> t' ->
  t.[sigma] >=> t'.[sigma].
Proof.
  intros H.
  revert sigma.
  induction H as [
    s s' t t' par_red_s_s' IHs par_red_t_t' IHt
    | v
    | s s' t t' par_red_s_s' IHs par_red_t_t' IHt
    | s s' par_red_s_s' IHs
  ]; intros sigma.
  - asimpl.
    pose proof (ParRed_Subst s.[up sigma] s'.[up sigma] t.[sigma] t'.[sigma]) as H.
    asimpl in H.
    apply H; [ apply IHs | apply IHt ].
  - apply par_red_refl.
  - apply ParRed_App; [ apply IHs | apply IHt ].
  - apply ParRed_Lam.
    asimpl.
    apply IHs.
Qed.

Lemma par_red_subst_up_equivalence (sigma sigma': var -> term):
  (forall v: var, sigma v >=> sigma' v) ->
  forall v: var, up sigma v >=> up sigma' v.
Proof.
  intros H.
  destruct v.
  - apply par_red_refl.
  - asimpl.
    apply par_red_subst.
    apply H.
Qed.

Lemma par_red_subst_par_red (s t: term) (sigma sigma': var -> term):
  (forall v: var, sigma v >=> sigma' v) ->
  s >=> t -> s.[sigma] >=> t.[sigma'].
Proof.
  intros Hv H.
  revert sigma sigma' Hv.
  induction H as [
    s s' t t' _ IHs _ IHt
    | v
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
  ]; intros sigma sigma' Hv.
  - asimpl.
    pose proof (ParRed_Subst s.[up sigma] s'.[up sigma'] t.[sigma] t'.[sigma']) as H.
    asimpl in H.
    apply H.
    + apply IHs.
      apply par_red_subst_up_equivalence.
      assumption.
    + apply IHt.
      assumption.
  - asimpl.
    apply Hv.
  - asimpl.
    apply ParRed_App.
    + apply IHs.
      assumption.
    + apply IHt.
      assumption.
  - asimpl.
    apply ParRed_Lam.
    apply IHs.
    apply par_red_subst_up_equivalence.
    assumption.
Qed.

Lemma beta_star_app_r (s s' t: term):
  s ~>* s' ->
  App s t ~>* App s' t.
Proof.
  intros Ht.
  induction Ht.
  - apply rt_step.
    apply Beta_AppL.
    assumption.
  - apply rt_refl.
  - apply rt_trans with (y := App y t); assumption.
Qed.

Lemma beta_star_app (s s' t t': term):
  s ~>* s' ->
  t ~>* t' ->
  App s t ~>* App s' t'.
Proof.
  intros beta_star_s_s' beta_star_t_t'.
  revert t t' beta_star_t_t'.
  induction beta_star_s_s' as [ x y H | x | x y z IHxy IHAppxy IHyz IHAppyz ]; intros t t' beta_star_t_t'.
  - apply rt_step in H.
    revert x y H.
    induction beta_star_t_t' as [ x' y' IH | x' | x' y' z' _ IHy _ IHz ]; intros x y H.
    + apply rt_trans with (y := App y x').
      * apply beta_star_app_r.
        assumption.
      * apply rt_step.
        apply Beta_AppR.
        assumption.
    + apply beta_star_app_r.
      assumption.
    + apply rt_trans with (y := App y y').
      * apply IHy.
        assumption.
      * apply IHz.
        apply rt_refl.
  - induction beta_star_t_t'.
    + apply rt_step.
      apply Beta_AppR.
      assumption.
    + apply rt_refl.
    + apply rt_trans with (y := App x y); assumption.
  - apply rt_trans with (y := App y t).
    + apply IHAppxy.
      apply rt_refl.
    + apply IHAppyz.
      assumption.
Qed. 

Lemma beta_star_lam (s s': term):
  s ~>* s' ->
  Lam s ~>* Lam s'.
Proof.
  intros beta_star_s_s'.
  induction beta_star_s_s' as [ s s' H | x | x y z IHxy IHAppxy IHyz IHAppyz ].
  - induction H; apply rt_step, Beta_Lam.
    + apply Beta_Subst.
      assumption.
    + apply Beta_AppL.
      assumption.
    + apply Beta_AppR.
      assumption.
    + apply Beta_Lam.
      assumption.
  - apply rt_refl.
  - apply rt_trans with (y := Lam y); assumption.
Qed. 

Lemma par_red_to_beta_star (s t : term):
  s >=> t -> s ~>* t.
Proof.
  intros H.
  induction H as [
    s s' t t' _ beta_star_s_s' _ beta_star_t_t'
    | v
    | s s' t t' _ beta_star_s_s' _ beta_star_t_t'
    | s s' _ beta_star_s_s'
  ].
  - apply rt_trans with (y := App (Lam s') t).
    + apply beta_star_app.
      * apply beta_star_lam.
        assumption.
      * apply rt_refl.
    + apply rt_trans with (y := App (Lam s') t').
      * apply beta_star_app; [ apply rt_refl | assumption ].
      * apply rt_step.
        apply Beta_Subst.
        reflexivity.
  - apply rt_refl.
  - apply beta_star_app; assumption.
  - apply beta_star_lam.
    assumption.
Qed.

Lemma beta_star_equiv_par_red_star (s t: term):
  s ~>* t <-> s >=>* t.
Proof.
  split.
  - intros H.
    induction H as [ t t' H | t | t t' t'' Ht IHt Ht' IHt' ].
    + apply rt_step.
      apply beta_to_par_red.
      assumption.
    + apply rt_refl.
    + apply rt_trans with (y := t'); assumption.
  - intros H.
    induction H as [ t t' H | t | t t' t'' Ht IHt Ht' IHt' ].
    + apply par_red_to_beta_star.
      assumption.
    + apply rt_refl.
    + apply rt_trans with (y := t'); assumption.
Qed.

Lemma lam_match : forall (s u : term) (f : term -> term),
  (exists s', s = Lam s' /\ (replace_lambda f s u) = f s') \/
  ((replace_lambda f s u) = u /\ ~exists s', s = Lam s').
Proof.
  intros s u f.
  destruct s as [ n | s1 s2 | s ].
  - right.
    split.
    + simpl.
      reflexivity.
    + intros [ t eq_t ].
      discriminate.
  - right.
    simpl.
    split.
    + reflexivity.
    + intros [ t eq_t ].
      discriminate.
  - simpl.
    left.
    exists s.
    split; reflexivity.
Qed.

Lemma max_par_red (t t': term):
  t >=> t' -> t' >=> par_red_max_reduction t.
Proof.
  intros Ht.
  induction Ht as [
    s s' t t' _ IHs _ IHt
    | v
    | s s' t t' par_red_s_s' IHs _ IHt
    | s s' _ IHs
  ]; asimpl.
  - apply par_red_subst_par_red.
    + intros v.
      destruct v.
      * asimpl.
        assumption.
      * asimpl.
        apply par_red_refl.
    + assumption.
  - apply par_red_refl.
  - set (f := fun s' => (par_red_max_reduction s').[par_red_max_reduction t/]).
    destruct (lam_match s (App (par_red_max_reduction s) (par_red_max_reduction t)) f) as [ [ u [ H1 H2 ] ] | [ H1 H2 ] ]; subst.
    + inversion par_red_s_s'; subst.
      inversion IHs; subst.
      apply ParRed_Subst; assumption.
    + destruct s as [ n | s1 s2 | s ]; simpl in IHs.
      * simpl.
        apply ParRed_App; assumption.
      * apply ParRed_App; assumption.
      * exfalso.
        apply H2.
        exists s.
        reflexivity.
  - apply ParRed_Lam.
    assumption.
Qed.

Lemma local_confluence_par_red: local_confluence par_red.
Proof.
  intros t u v Hu Hv.
  exists (par_red_max_reduction t).
  split; apply max_par_red; assumption.
Qed.

Lemma par_red_left_cr (t u v : term):
  par_red t u ->
  par_red* t v ->
  exists (w : term), par_red* u w /\ par_red v w.
Proof.
  intros Hu Hv.
  revert u Hu.
  induction Hv as [ t v Hv | t | t v v' Hv IHv Hv' IHv']; intros u Hu.
  - destruct (local_confluence_par_red t u v Hu Hv) as [ w [ H1 H2 ] ].
    exists w.
    split; [ apply rt_step | ]; assumption.
  - exists u.
    split; [ apply rt_refl | assumption ].
  - specialize (IHv _ Hu) as [ u' [ H1 H2 ] ].
    specialize (IHv' _ H2) as [ w [ H3 H4 ] ].
    exists w.
    split; [ | assumption ].
    apply rt_trans with (y := u'); assumption.
Qed.

Lemma par_red_cr: CR par_red.
Proof.
  intros t u v Hu Hv.
  revert v Hv.
  induction Hu as [ t u Hu | t | t u u' Hu IHu Hu' IHu' ]; intros v Hv.
  - destruct (par_red_left_cr t u v Hu Hv) as [ w [ H1 H2 ] ].
    exists w.
    split; [ | apply rt_step ]; assumption.
  - exists v.
    split; [ assumption | apply rt_refl ].
  - destruct (IHu _ Hv) as [ w [ H1 H2 ] ].
    destruct (IHu' _ H1) as [ w' [ H3 H4 ] ].
    exists w'.
    split; [ assumption | ].
    apply rt_trans with (y := w); assumption.
Qed.

Theorem ChurchRosser: CR beta.
Proof.
  intros t u v Hu Hv.
  rewrite beta_star_equiv_par_red_star in Hu, Hv.
  specialize (par_red_cr t u v Hu Hv) as [ w [ H1 H2 ] ].
  exists w.
  rewrite <- beta_star_equiv_par_red_star in H1, H2.
  split; assumption.
Qed.
