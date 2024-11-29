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

  | ParRed_Pair (s s' t t': term):
    s >=> s' ->
    t >=> t' ->
    Pair s t >=> Pair s' t'

  | ParRed_Pr1 (s s': term):
    s >=> s' ->
    Pr1 s >=> Pr1 s'

  | ParRed_Pr2 (s s': term):
    s >=> s' ->
    Pr2 s >=> Pr2 s'

  | ParRed_Pr1_Pair (s s' t: term):
    s >=> s' ->
    Pr1 (Pair s t) >=> s'

  | ParRed_Pr2_Pair (s t t': term):
    t >=> t' ->
    Pr2 (Pair s t) >=> t'

  | ParRed_Pat (s s' t t' u u': term):
    s >=> s' ->
    t >=> t' ->
    u >=> u' ->
    Pat s t u >=> Pat s' t' u'

  | ParRed_In1 (s s': term):
    s >=> s' ->
    In1 s >=> In1 s'

  | ParRed_In2 (s s': term):
    s >=> s' ->
    In2 s >=> In2 s'

  | ParRed_Pat_In1 (s s' t t' u: term):
    s >=> s' ->
    t >=> t' ->
    Pat (In1 s) t u >=> t'.[s'/]

  | ParRed_Pat_In2 (s s' t u u': term):
    s >=> s' ->
    u >=> u' ->
    Pat (In2 s) t u >=> u'.[s'/]

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
  | Pair s t => Pair (par_red_max_reduction s) (par_red_max_reduction t)
  | Pr1 (Pair s t) => par_red_max_reduction s
  | Pr2 (Pair s t) => par_red_max_reduction t
  | Pr1 s => Pr1 (par_red_max_reduction s)
  | Pr2 s => Pr2 (par_red_max_reduction s)
  | In1 s => In1 (par_red_max_reduction s)
  | In2 s => In2 (par_red_max_reduction s)
  | Pat (In1 s) t u => (par_red_max_reduction t).[(par_red_max_reduction s)/]
  | Pat (In2 s) t u => (par_red_max_reduction u).[(par_red_max_reduction s)/]
  | Pat s t u => Pat (par_red_max_reduction s) (par_red_max_reduction t) (par_red_max_reduction u)
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

Definition replace_in1_in2 (f1 f2: term -> term) (s u: term): term :=
  match s with
  | In1 s' => f1 s'
  | In2 s' => f2 s'
  | _ => u
  end.

Lemma par_red_refl (t: term):
  t >=> t.
Proof.
  induction t.
  - apply ParRed_Var.
  - apply ParRed_App; assumption.
  - apply ParRed_Lam. assumption.
  - apply ParRed_Pair; assumption.
  - apply ParRed_Pr1; assumption.
  - apply ParRed_Pr2; assumption.
  - apply ParRed_Pat; assumption.
  - apply ParRed_In1. assumption.
  - apply ParRed_In2. assumption.
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
  - apply ParRed_Pair; [ assumption | apply par_red_refl ].
  - apply ParRed_Pair; [ apply par_red_refl | assumption ].
  - apply ParRed_Pr1. assumption.
  - apply ParRed_Pr2. assumption.
  - apply ParRed_Pr1_Pair. apply par_red_refl.
  - apply ParRed_Pr2_Pair. apply par_red_refl.
  - apply ParRed_Pat; [ assumption | | ]; apply par_red_refl.
  - apply ParRed_Pat; [ | assumption | ]; apply par_red_refl.
  - apply ParRed_Pat; [ | | assumption ]; apply par_red_refl.
  - now apply ParRed_In1.
  - now apply ParRed_In2.
  - subst. apply ParRed_Pat_In1; apply par_red_refl.
  - subst. apply ParRed_Pat_In2; apply par_red_refl.
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
  - apply ParRed_Pair; [apply IHs | apply IHt].
  - apply ParRed_Pr1. apply IHs.
  - apply ParRed_Pr2. apply IHs.
  - apply ParRed_Pr1_Pair. apply IHs.
  - apply ParRed_Pr2_Pair. apply IHt.
  - apply ParRed_Pat; [ apply IHs | apply IHt | apply IHu ].
  - apply ParRed_In1. apply IHs.
  - apply ParRed_In2. apply IHs.
  - asimpl.
    pose proof (ParRed_Pat_In1 s.[sigma] s'.[sigma] t.[up sigma] t'.[up sigma] u.[up sigma]) as H.
    asimpl in H. apply H; [ apply IHs | apply IHt ].
  - asimpl.
    pose proof (ParRed_Pat_In2 s.[sigma] s'.[sigma] t.[up sigma] u.[up sigma] u'.[up sigma]) as H.
    asimpl in H. apply H; [ apply IHs | apply IHu ].
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
  - apply ParRed_Pair; [ apply (IHs _ _ Hv) | apply (IHt _ _ Hv) ].
  - apply ParRed_Pr1. apply (IHs _ _ Hv).
  - apply ParRed_Pr2. apply (IHs _ _ Hv).
  - apply ParRed_Pr1_Pair. apply (IHs _ _ Hv).
  - apply ParRed_Pr2_Pair. apply (IHt _ _ Hv).
  - apply ParRed_Pat; [apply IHs | apply IHt | apply IHu].
    + assumption.
    + now apply par_red_subst_up_equivalence.
    + now apply par_red_subst_up_equivalence.
  - apply ParRed_In1. now apply IHs.
  - apply ParRed_In2. now apply IHs.
  - pose proof (ParRed_Pat_In1 s.[sigma] s'.[sigma'] t.[up sigma] t'.[up sigma'] u.[up sigma]) as H.
    asimpl in H. asimpl. apply H.
    + now apply IHs.
    + apply IHt. now apply par_red_subst_up_equivalence.
  - pose proof (ParRed_Pat_In2 s.[sigma] s'.[sigma'] t.[up sigma] u.[up sigma] u'.[up sigma']) as H.
    asimpl in H. asimpl. apply H.
    + now apply IHs.
    + apply IHu. now apply par_red_subst_up_equivalence.
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
  - apply rt_trans with (y := App (Lam s') t).
    + apply beta_star_app.
      * now apply beta_star_lam.
      * apply rt_refl.
    + apply rt_trans with (y := App (Lam s') t').
      * apply beta_star_app; [ apply rt_refl | assumption ].
      * apply rt_step.
        apply Beta_Subst.
        reflexivity.
  - apply rt_refl.
  - apply beta_star_app; assumption.
  - apply beta_star_lam. assumption.
  - apply beta_star_f2; try assumption.
    + apply Beta_Pair1.
    + apply Beta_Pair2.
  - apply beta_star_f1.
    + apply Beta_Pr1.
    + assumption.
  - apply beta_star_f1.
    + apply Beta_Pr2.
    + assumption.
  - apply rt_trans with (y := s); [| assumption ].
    apply rt_step. apply Beta_Pr1_Pair.
  - apply rt_trans with (y := t); [| assumption ].
    apply rt_step. apply Beta_Pr2_Pair.
  - apply beta_star_pat; assumption.
  - apply beta_star_f1; [apply Beta_In1 | assumption ].
  - apply beta_star_f1; [apply Beta_In2 | assumption ].
  - apply rt_trans with (Pat (In1 s') t u).
    + apply beta_star_pat.
      2, 3: apply rt_refl.
      apply beta_star_f1.
      * apply Beta_In1.
      * assumption.
    + apply rt_trans with (Pat (In1 s') t' u).
      * apply beta_star_pat.
        1, 3: apply rt_refl.
        assumption.
      * apply rt_step. now apply Beta_Pat_In1.
  - apply rt_trans with (Pat (In2 s') t u).
    + apply beta_star_pat.
      2, 3: apply rt_refl.
      apply beta_star_f1.
      * apply Beta_In2.
      * assumption.
    + apply rt_trans with (Pat (In2 s') t u').
      * apply beta_star_pat.
        1, 2: apply rt_refl.
        assumption.
      * apply rt_step. now apply Beta_Pat_In2.
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
  destruct s as [ n | s1 s2 | s | s1 s2 | s | s | s1 s2 s3 | s | s ].
  1, 2, 4, 5, 6, 7, 8, 9: right; simpl; split; try reflexivity; intros [t eq]; discriminate.
  simpl. left.
  exists s. split; reflexivity.
Qed.

Lemma pair_match : forall (s u: term) (f : term -> term -> term),
    (exists s' t', s = Pair s' t' /\ replace_pair f s u = f s' t') \/
    (replace_pair f s u = u /\ ~ exists s' t', s = Pair s' t').
Proof.
  intros [n | s1 s2 | s | s1 s2 | s | s | s1 s2 s3 | s | s] u f.
  1, 2, 3, 5, 6, 7, 8, 9:
    simpl; right; split; try reflexivity;
    intros [s' [t' eq]]; discriminate.
  left. simpl. exists s1, s2. split; reflexivity.
Qed.

Lemma in1_in2_match : forall (s u: term) (f1 f2: term -> term),
    (exists s', s = In1 s' /\ replace_in1_in2 f1 f2 s u = f1 s') \/
    (exists s', s = In2 s' /\ replace_in1_in2 f1 f2 s u = f2 s') \/
    (replace_in1_in2 f1 f2 s u = u /\ ~ (exists s', s = In1 s') /\ ~ (exists s', s = In2 s')).
Proof.
  intros [] ? ? ?.
  1, 2, 3, 4, 5, 6, 7:
    simpl; right; right; repeat split; try reflexivity;
    intros [s' eq]; discriminate.
  - left. exists s; split; reflexivity.
  - right. left. exists s; split; reflexivity.
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
    destruct (lam_match s (App (par_red_max_reduction s) (par_red_max_reduction t)) f) as
      [ [ u [ H1 H2 ] ] | [ H1 H2 ] ]; subst.
    + inversion par_red_s_s'; subst.
      inversion IHs; subst.
      apply ParRed_Subst; assumption.
    + destruct s; simpl in IHs.
      3: exfalso; apply H2; exists s; reflexivity.
      all: apply ParRed_App; assumption.
  - apply ParRed_Lam.
    assumption.
  - apply ParRed_Pair; assumption.
  - set (f := fun (s t : term) => par_red_max_reduction s).
    destruct (pair_match s (Pr1 (par_red_max_reduction s)) f) as [[u [v [H1 H2]]] | [H1 H2]]; subst.
    + simpl in IHs. inversion par_red_s_s'; subst.
      inversion IHs; subst. apply ParRed_Pr1_Pair. assumption.
    + destruct s; simpl in IHs.
      4: exfalso; apply H2; exists s1, s2; reflexivity.
      all: apply ParRed_Pr1; assumption.
  - set (f := fun (s t : term) => par_red_max_reduction s).
    destruct (pair_match s (Pr2 (par_red_max_reduction s)) f) as [[u [v [H1 H2]]] | [H1 H2]]; subst.
    + simpl in IHs. inversion par_red_s_s'; subst.
      inversion IHs; subst. apply ParRed_Pr2_Pair. assumption.
    + destruct s; simpl in IHs.
      4: exfalso; apply H2; exists s1, s2; reflexivity.
      all: apply ParRed_Pr2; assumption.
  - assumption.
  - assumption.
  - set (f1 := fun s0 => (par_red_max_reduction t).[par_red_max_reduction s0/]).
    set (f2 := fun s0 => (par_red_max_reduction u).[par_red_max_reduction s0/]).
    destruct (in1_in2_match s (Pat (par_red_max_reduction s)
                             (par_red_max_reduction t) (par_red_max_reduction u)) f1 f2)
    as [ [v [H1 H2]] | [ [v [H1 H2]] | [H1 [H2 H3] ] ]]; subst.
    + simpl in IHs. inversion par_red_s_s'. subst.
      inversion IHs. subst. apply ParRed_Pat_In1; assumption.
    + simpl in IHs. inversion par_red_s_s'. subst.
      inversion IHs. subst. apply ParRed_Pat_In2; assumption.
    + destruct s; simpl in IHs.
      9: exfalso; apply H3; exists s; reflexivity.
      8: exfalso; apply H2; exists s; reflexivity.
      all: apply ParRed_Pat; assumption.
  - now apply ParRed_In1.
  - now apply ParRed_In2.
  - apply par_red_subst_par_red.
    + intros [| v ]; simpl.
      * assumption.
      * apply par_red_refl.
    + assumption.
  - apply par_red_subst_par_red.
    + intros [| v ]; simpl.
      * assumption.
      * apply par_red_refl.
    + assumption.
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
