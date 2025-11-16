From Coq Require Import Utf8.
From Coq Require Import Arith Lia.
From FormArith Require Import Base.
From FormArith.LambdaCube Require Import Term.

Reserved Notation "t [≻] u" (at level 70).
Reserved Notation "t ≻ u" (at level 70).
Reserved Notation "t ≻+ u" (at level 70).
Reserved Notation "t ≻* u" (at level 70).
Reserved Notation "t ≅ u" (at level 70).

Inductive head_step {n : nat} : term n → term n → Prop :=
| beta_red
    (ty : term n)
    (body : term (S n))
    (arg : term n) : App (Abs ty body) arg [≻] bind (bind_first arg) body
where "t [≻] u" := (head_step t u).

Inductive step {n : nat} : term n → term n → Prop :=
| ctx_red {k} (K : ctx n k) (t u : term k) :
  t [≻] u → fill K t ≻ fill K u
where "t ≻ u" := (step t u).

Lemma step_under_context {n k} (K: ctx n k) t u : t ≻ u -> fill K t ≻ fill K u.
Proof.
  destruct 1 as [K']. do 2 rewrite <- fill_fillK. constructor. assumption.
Qed.

Inductive Rplus {A} (R: relation A) a b : Prop :=
| add_last_R m : Rplus R a m -> R m b -> Rplus R a b
| Rclot_plus : R a b -> Rplus R a b.

Notation "t ≻+ u" := (Rplus step t u).

Lemma Rplus_trans {A} (R: relation A) x y z : Rplus R x y -> Rplus R y z -> Rplus R x z.
Proof.
  induction 2.
  - econstructor; eauto.
  - econstructor; eauto.
Qed.

Lemma add_first {A}  (R: relation A) x y z : R x y -> Rplus R y z -> Rplus R x z.
  induction 2.
  - econstructor; eauto.
  - econstructor; eauto. constructor. auto.
Qed.

Inductive Rstar {A} (R: relation A) a : A -> Prop :=
| Rstar_refl : Rstar R a a
| Rclot_plus_star b : Rplus R a b -> Rstar R a b.

Notation "t ≻* u" := (Rstar step t u).

Lemma step_star_context {n k} (K: ctx n k) t u : t ≻* u -> fill K t ≻* fill K u.
Proof.
  destruct 1; constructor. induction H.
  - econstructor; try eassumption. apply step_under_context. assumption.
  - constructor. apply step_under_context. assumption.
Qed.

Lemma Rstar_trans {A} (R: relation A) x y z : Rstar R x y -> Rstar R y z -> Rstar R x z.
Proof.
  destruct 1; auto.
  destruct 1.
  - constructor. assumption.
  - constructor. eapply Rplus_trans; eassumption.
Qed.

Inductive Requiv {A} (R: relation A) a : A -> Prop :=
| Rclot_plus_equiv b : Rplus R a b -> Requiv R a b
| Rclot_plus_equiv_r b : Rplus R b a -> Requiv R a b
| Requiv_refl : Requiv R a a.

Notation "t ≅ u" := (Requiv step t u).

Reserved Notation "t ⪼ u" (at level 70).
Reserved Notation "t ⪼+ u" (at level 70).
Reserved Notation "t ⪼* u" (at level 70).

Inductive par_step {n: nat} : term n -> term n -> Prop :=
| par_step_var i : Var i ⪼ Var i
| par_step_sort s : Srt s ⪼ Srt s
| par_step_pi t1 t2 u1 u2 : t1 ⪼ u1 -> t2 ⪼ u2 -> Pi t1 t2 ⪼ Pi u1 u2
| par_step_abs t1 t2 u1 u2 : t1 ⪼ u1 -> t2 ⪼ u2 -> Abs t1 t2 ⪼ Abs u1 u2
| par_step_app t1 t2 u1 u2 : t1 ⪼ u1 -> t2 ⪼ u2 -> App t1 t2 ⪼ App u1 u2
| par_step_redex T f arg f' arg' :
  f ⪼ f' -> arg ⪼ arg' -> App (Abs T f) arg ⪼ bind (bind_first arg') f'
where "t ⪼ u" := (par_step t u).

Notation "t ⪼+ u" := (Rplus par_step t u).
Notation "t ⪼* u" := (Rstar par_step t u).

Lemma par_refl {n} (t : term n) : t ⪼ t.
Proof.
  induction t; constructor; assumption.
Qed.

Fixpoint par_max {n} (t: term n) : term n :=
  match t with
  | App (Abs _ f) arg => bind (bind_first (par_max arg)) (par_max f)
  | Srt _ | Var _ => t
  | Pi A B => Pi (par_max A) (par_max B)
  | Abs T f => Abs (par_max T) (par_max f)
  | App a b => App (par_max a) (par_max b)
  end.

Lemma par_par_max {n} (t: term n) : t ⪼ par_max t.
  induction t; simpl; try solve [constructor; assumption].
  destruct t1; try solve [constructor; assumption].
  simpl in *. inversion_clear IHt1.
  constructor; assumption.
Qed.

Lemma ren_preserves_par {n k} (σ: {i | i < n} -> {i | i < k}) t u :
  t ⪼ u -> ren σ t ⪼ ren σ u.
Proof.
   induction 1 in k, σ |- *; simpl; try constructor; auto.
   rewrite ren_bind. specialize (IHpar_step1 _ (lift σ)). specialize (IHpar_step2 _ σ).
   enough (
       e : bind (ren σ ∘ bind_first arg') f' =
             bind (bind_first (ren σ arg')) (ren (lift σ) f')
     ) by (rewrite e; constructor; assumption). clear. rewrite bind_ren.
   apply bind_ext.
   intro. unfold lift, bind_first. destruct (lt_dec _ _); simpl.
   - pose proof (proj2_sig (σ (exist _ (proj1_sig i) l))). simpl in *.
     destruct (lt_dec _ _); try tauto. f_equal. apply sig_lt_ext. reflexivity.
   - destruct (lt_dec _ _); try lia. reflexivity.
Qed.

Lemma par_max_is_max {n} (t t': term n) : t ⪼ t' -> t' ⪼ par_max t.
Proof.
  induction 1; simpl in *; try solve [constructor; assumption].
  - destruct t1; try solve [constructor; assumption].
    simpl in *. inversion H; subst; clear H. inversion_clear IHpar_step1.
    constructor; assumption.
  - revert IHpar_step1 IHpar_step2. clear. generalize (par_max f), (par_max arg). clear.
    rename f' into f, arg' into arg. intros f' arg' fred argred.
    cut (forall i, bind_first arg i ⪼ bind_first arg' i); swap 1 2.
    { unfold bind_first. intro. destruct (lt_dec _ _); try assumption; constructor. }
    generalize (bind_first arg) as σ1, (bind_first arg') as σ2.
    clear arg arg' argred. generalize dependent n. fix IH 4.
    destruct 1; simpl.
    + intros ? ? H. apply H.
    + constructor.
    + constructor; auto. apply IH; try assumption. unfold lift_bind.
      intro. destruct (lt_dec _ _); try solve [constructor].
      apply ren_preserves_par. apply H.
    + constructor; auto. apply IH; try assumption. unfold lift_bind.
      intro. destruct (lt_dec _ _); try solve [constructor].
      apply ren_preserves_par. apply H.
    + constructor; auto.
    + intros. rewrite bind_comp.
      apply IH with (σ1 := lift_bind σ1) (σ2 := lift_bind σ2) in fred1 as IHf; swap 1 2.
      { unfold lift_bind. intro. destruct (lt_dec _ _); try solve [constructor].
        apply ren_preserves_par. apply H. }
      apply IH with (σ1 := σ1) (σ2 := σ2) in fred2 as IHarg; try assumption.
      enough (
          e : bind (bind σ2 ∘ bind_first arg') f' =
                bind (bind_first (bind σ2 arg')) (bind (lift_bind σ2) f')
        ) by (rewrite e; constructor; try assumption).
      rewrite bind_comp. apply bind_ext.
      intro. unfold lift_bind, bind_first at 1.
      destruct (lt_dec _ _).
      * simpl. rewrite bind_ren.
        generalize (σ2 (exist _ (proj1_sig i) l)).
        intro. clear. assert (forall i, (bind_first (bind σ2 arg') ∘ weaken) i = Var i).
        { intro. unfold weaken. unfold bind_first. simpl. pose proof (proj2_sig i).
          destruct (lt_dec _ _); try tauto. f_equal. apply sig_lt_ext. reflexivity. }
        revert H. generalize (bind_first (bind σ2 arg') ∘ weaken). clear.
        induction t; simpl; auto; intros; f_equal; auto; apply IHt2.
        -- unfold lift_bind. intro. destruct (lt_dec _ _).
           ++ rewrite H. simpl. unfold weaken. f_equal. apply sig_lt_ext. reflexivity.
           ++ f_equal. apply sig_lt_ext. pose proof (proj2_sig i). simpl in *. lia.
        -- unfold lift_bind. intro. destruct (lt_dec _ _).
           ++ rewrite H. simpl. unfold weaken. f_equal. apply sig_lt_ext. reflexivity.
           ++ f_equal. apply sig_lt_ext. pose proof (proj2_sig i). simpl in *. lia.
      * simpl. unfold bind_first. simpl. destruct (lt_dec n n); try lia. reflexivity.
Qed.

Lemma diamond_par {n} (t u u': term n) : t ⪼ u -> t ⪼ u' -> exists v, u ⪼ v /\ u' ⪼ v.
  intros. exists (par_max t). split; apply par_max_is_max; assumption.
Qed.

Lemma left_star_par_commute {n} (t u u': term n) : t ⪼* u -> t ⪼ u' -> exists v, u ⪼ v /\ u' ⪼* v.
Proof.
  destruct 1. { intro. exists u'. intuition. constructor. }
  induction H in u' |- *.
  - intro redr. specialize (IHRplus _ redr) as IHu'. destruct IHu' as [x []].
    destruct (diamond_par m b x); try assumption. intuition. exists x0. intuition.
    destruct H2.
    + do 2 constructor. assumption.
    + constructor. econstructor; eassumption.
  - intro. destruct (diamond_par t b u'); try assumption. exists x. intuition. do 2 constructor.
    assumption.
Qed.

Lemma confluence_par {n} (t u u': term n) : t ⪼* u -> t ⪼* u' -> exists v, u ⪼* v /\ u' ⪼* v.
Proof.
  destruct 2. { eexists. intuition try eassumption. constructor. }
  induction H0; firstorder.
  - destruct (left_star_par_commute _ _ _ H3 H1). exists x0. intuition. constructor. destruct H2.
    + constructor. assumption.
    + econstructor; eassumption.
  - destruct (left_star_par_commute _ _ _ H H0). exists x. intuition. do 2 constructor. assumption.
Qed.

Lemma step_incl_par {n} (t u: term n) : t ≻ u -> t ⪼ u.
Proof.
  destruct 1.
  induction K; simpl; try solve [constructor; auto using par_refl].
  destruct H. constructor; apply par_refl.
Qed.

Lemma step_star_incl_par_star {n} (t u: term n) : t ≻* u -> t ⪼* u.
Proof.
  destruct 1; constructor.
  induction H.
  - econstructor; try eassumption. apply step_incl_par. assumption.
  - constructor. apply step_incl_par. assumption.
Qed.

Lemma par_incl_step_star {n} (t u: term n) : t ⪼ u -> t ≻* u.
  induction 1; try solve [constructor].
  - eapply Rstar_trans.
    + change (Pi t1 t2) with (fill (PiL Hole t2) t1). apply step_star_context. eassumption.
    + simpl. change (Pi u1 ?x) with (fill (PiR u1 Hole) x). apply step_star_context. assumption.
  - eapply Rstar_trans.
    + change (Abs t1 t2) with (fill (AbsL Hole t2) t1). apply step_star_context. eassumption.
    + simpl. change (Abs u1 ?x) with (fill (AbsR u1 Hole) x). apply step_star_context. assumption.
  - eapply Rstar_trans.
    + change (App t1 t2) with (fill (AppL Hole t2) t1). apply step_star_context. eassumption.
    + simpl. change (App u1 ?x) with (fill (AppR u1 Hole) x). apply step_star_context. assumption.
  - apply Rstar_trans with (y := App (Abs T f') arg).
    + change (App (Abs T ?x) ?y) with (fill (AppL (AbsR T Hole) y) x).
      apply step_star_context. assumption.
    + apply Rstar_trans with (y := App (Abs T f') arg').
      * change (App ?x ?y) with (fill (AppR x Hole) y). apply step_star_context. assumption.
      * do 2 constructor. change (?x ≻ ?y) with (fill Hole x ≻ fill Hole y). do 2 constructor.
Qed.

Lemma par_star_incl_step_star {n} (t u: term n) : t ⪼* u -> t ≻* u.
Proof.
  destruct 1; [constructor |].
  induction H.
  - eapply Rstar_trans; try eassumption. apply par_incl_step_star. assumption.
  - apply par_incl_step_star. assumption.
Qed.

Lemma confluence_step {n} (t u u': term n) : t ≻* u -> t ≻* u' -> exists v, u ≻* v /\ u' ≻* v.
Proof.
  intros tl tr. apply step_star_incl_par_star in tl, tr.
  destruct (confluence_par _ _ _ tl tr) as [v]. exists v. intuition auto using par_star_incl_step_star.
Qed.
