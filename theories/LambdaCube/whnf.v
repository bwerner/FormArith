From Coq Require Import Utf8.
From Coq Require Import Arith Lia.
From FormArith Require Import Base.
From FormArith.LambdaCube Require Import Term Operational Typing SN.

Reserved Notation "x w≻ y" (at level 70).
Reserved Notation "x w≻+ y" (at level 70).
Reserved Notation "x w≻* y" (at level 70).

Inductive wctx n : Type :=
| wHole : wctx n
| wApp : wctx n -> term n -> wctx n.

Arguments wHole {n}.
Arguments wApp {n}.

Fixpoint wfill {n} (K: wctx n) (t: term n) :=
  match K with
  | wHole => t
  | wApp K u => App (wfill K t) u
  end.

Fixpoint wctx_to_ctx {n} (K: wctx n) : ctx n n :=
  match K with
  | wHole => Hole
  | wApp K u => AppL (wctx_to_ctx K) u
  end.

Lemma fill_wctx {n} (K: wctx n) u : fill (wctx_to_ctx K) u = wfill K u.
Proof.
  induction K; simpl; f_equal; auto.
Qed.

Inductive wstep {n} : term n -> term n -> Prop :=
| wctx_red {K: wctx n} {t u: term n} : t [≻] u -> wfill K t w≻ wfill K u
where "x w≻ y" := (wstep x y).

Notation "x w≻+ y" := (Rplus wstep x y).
Notation "x w≻* y" := (Rstar wstep x y).

Lemma wstep_is_step {n} {t u: term n} : t w≻ u -> t ≻ u.
Proof.
  destruct 1. rewrite <- !fill_wctx. constructor. assumption.
Qed.

Lemma wstep_plus_is_step_plus {n} {t u: term n} : t w≻+ u -> t ≻+ u.
Proof.
  induction 1.
  - econstructor; eauto using wstep_is_step.
  - constructor. apply wstep_is_step. assumption.
Qed.

Lemma wstep_star_is_step_star {n} {t u: term n} : t w≻* u -> t ≻* u.
Proof.
  destruct 1.
  - constructor.
  - constructor. apply wstep_plus_is_step_plus. assumption.
Qed.

Inductive neutral {n} : term n -> Prop :=
| neutral_var i : neutral (Var i)
| neutral_srt s : neutral (Srt s)
| neutral_pi A B : neutral (Pi A B)
| neutral_app t u : neutral t -> neutral (App t u)
.

Inductive whnf {n} : term n -> Prop :=
| whnf_abs A t : whnf (Abs A t)
| whnf_neutral t : neutral t -> whnf t.

Fixpoint is_neutral {n} (t: term n) : {neutral t} + {¬ neutral t} :=
  match t with
  | Var i => left (neutral_var i)
  | Pi A B => left (neutral_pi A B)
  | Abs A t => right (
                  fun (H: neutral (Abs A t)) =>
                    match H in neutral t return
                          match t with Abs _ _ => False | _ => True end with
                    | neutral_var _ | _ => I
                    end
                )
  | App t u =>
      match is_neutral t with
      | left H => left (neutral_app t u H)
      | right nneu => right (
                         fun (H: neutral (App t u)) =>
                           nneu
                             match H in neutral x return
                                   match x with App t u => neutral t | _ => True end
                             with
                             | neutral_app t u H => H
                             | _ => I
                             end
                       )
      end
  | Srt s => left (neutral_srt _)
  end.

Definition is_whnf {n} (t : term n) : {whnf t} + {¬ whnf t} :=
  match t with
  | Abs A t => left (whnf_abs A t)
  | t =>
      match is_neutral t with
      | left H => left (whnf_neutral t H)
      | right nnet =>
          right (
              fun (H: whnf t) =>
                nnet
                  match H in whnf t return match t with Abs _ _ => True | t => neutral t end with
                  | whnf_abs _ _ => I
                  | whnf_neutral t1 H =>
                      match t1 as t1
                            return
                            neutral t1 -> match t1 with Abs _ _ => True | _ => neutral t1 end
                      with
                      | Abs _ _ => fun H => I
                      | _ => fun H => H
                      end H
                  end
            )
      end
  end.

Lemma neutral_not_wstep {n} {t u: term n} : neutral t -> ¬(t w≻ u).
  induction 1 in u |- *; inversion 1; subst; destruct K; simpl in *; try discriminate; subst.
  - inversion H1.
  - inversion H1.
  - inversion H1.
  - inversion H2. subst. inversion H.
  - inversion H1; subst; clear H1. eapply IHneutral. constructor. eassumption.
Qed.

Lemma whnf_not_wstep {n} {t u: term n} : whnf t -> ¬(t w≻ u).
Proof.
  destruct 1.
  - inversion 1; subst. destruct K; try discriminate. simpl in *. subst. inversion H1.
  - apply neutral_not_wstep. assumption.
Qed.

Lemma not_wstep_whnf {n} {t: term n} : (forall u, ¬(t w≻ u)) -> whnf t.
Proof.
  destruct t; do 2 constructor. induction t1; try constructor.
  - exfalso. eapply H. change (?x w≻ ?y) with (wfill wHole x w≻ wfill wHole y).
    constructor. constructor.
  - eapply IHt1_1. intros ? red. inversion red. subst. eapply H.
    inversion red. subst. rewrite <- H0. change (App (wfill ?K ?x) ?y) with (wfill (wApp K y) x).
    constructor. eassumption.
Qed.

Lemma SN_app : ∀ {n} {e1 e2: term n}, SN (App e1 e2) -> SN e1.
Proof.
  fix IH 4.
  destruct 1. constructor. intros u red. apply (IH _ _ e2).
  apply (H (App u e2)). change (App ?x ?y) with (fill (AppL Hole y) x).
  apply step_under_context. assumption.
Qed.

Fixpoint wh_next_step {n} (t : term n) : option (term n) :=
  match t with
  | App (Abs A t) u => Some (bind (bind_first u) t)
  | App t u =>
      match wh_next_step t with
      | Some t => Some (App t u)
      | None => None
      end
  | _ => None
  end.

Lemma wh_next_step_some {n} {t u: term n} : wh_next_step t = Some u -> t w≻ u.
Proof.
  induction t in u |- *; simpl; try discriminate. clear IHt2.
  destruct t1; try discriminate.
  - inversion 1; subst. clear H. change (?x w≻ ?y) with (wfill wHole x w≻ wfill wHole y).
    constructor. constructor.
  - destruct (wh_next_step _); try discriminate. intro. inversion H; subst. clear H.
    specialize (IHt1 _ eq_refl). inversion IHt1. subst.
    change (App (wfill K ?x) ?y) with (wfill (wApp K y) x). constructor. assumption.
Qed.

Lemma wh_next_step_none {n} {t: term n} : wh_next_step t = None -> whnf t.
Proof.
  induction t; simpl; try solve [constructor | do 2 constructor].
  destruct (wh_next_step t1).
  - destruct t1; discriminate.
  - specialize (IHt1 eq_refl). destruct IHt1; try discriminate.
    constructor. constructor. assumption.
Qed.

Fixpoint whnormalize_SN {n} (t: term n) (H: SN t) {struct H} : term n :=
  match H with
  | SN_on _ H => 
      match wh_next_step t as x return wh_next_step t = x -> term n with
      | None => fun e => t
      | Some x => fun e => whnormalize_SN x (H _ (wstep_is_step (wh_next_step_some e)))
      end eq_refl
  end.

Lemma whnormalize_SN_whnf {n} (t: term n) (H: SN t) : whnf (whnormalize_SN t H).
Proof.
  generalize dependent n. fix IH 3.
  destruct H. simpl. generalize (@eq_refl _ (wh_next_step t)).
  destruct (wh_next_step t) at 2 3.
  - intro. apply IH.
  - apply wh_next_step_none.
Qed.

Lemma whnormalize_SN_wstep_star {n} (t: term n) (H: SN t) : t w≻* whnormalize_SN t H.
Proof.
  revert n t H. fix IH 3. destruct H; simpl. generalize (@eq_refl _ (wh_next_step t)).
  destruct (wh_next_step t) at 2 3.
  - intro. eapply Rstar_trans; swap 1 2.
    + apply IH.
    + do 2 constructor. apply wh_next_step_some. assumption.
  - constructor.
Qed.

Lemma whnormalize_SN_step_star {n} (t: term n) (H: SN t) : t ≻* whnormalize_SN t H.
Proof.
  apply wstep_star_is_step_star, whnormalize_SN_wstep_star.
Qed.

Definition whnormalize_typed {n} (t: term n) (H: exists Sc Γ T, Γ ⊢(Sc) t: T) : term n :=
  whnormalize_SN t (
      let '(ex_intro _ Sc (ex_intro _ Γ (ex_intro _ T H))) := H in typing_SN _ _ _ H
    ).

Lemma whnormalize_typed_whnf {n} (t: term n) (H: exists Sc Γ T, Γ ⊢(Sc) t: T) :
  whnf (whnormalize_typed t H).
  apply whnormalize_SN_whnf.
Qed.

Lemma whnormalize_typed_wstep_star {n} (t: term n) (H: exists Sc Γ T, Γ ⊢(Sc) t: T) :
  t w≻* whnormalize_typed t H.
Proof.
  apply whnormalize_SN_wstep_star.
Qed.

Lemma whnormalize_typed_step_star {n} (t: term n) (H: exists Sc Γ T, Γ ⊢(Sc) t: T) :
  t ≻* whnormalize_typed t H.
Proof.
  apply whnormalize_SN_step_star.
Qed.

Lemma whnormalize_typed_preserves {n} (t: term n) (H: exists Sc Γ T, Γ ⊢(Sc) t: T) :
  forall Sc Γ T, Γ ⊢(Sc) t : T -> Γ ⊢(Sc) whnormalize_typed t H : T.
Proof.
  intros. eapply subject_reduction; try eassumption.
  apply whnormalize_typed_step_star.
Qed.

Definition whnormalize_type_of {n} (T: term n) (H: exists Sc Γ t, Γ ⊢(Sc) t: T) : term n :=
  match T as T return (exists _ _ _, _ ⊢(_) _: T) -> term n with
  | Srt Box => fun _ => T
  | T =>
      fun H => whnormalize_typed T (
                let '(ex_intro _ Sc (ex_intro _ Γ (ex_intro _ T H))) := H in
                match srt_typing H with
                | or_introl e => ltac:(discriminate)
                | or_intror (ex_intro _ s H) =>
                    ex_intro _ Sc (ex_intro _ Γ (ex_intro _ (Srt s) H))
                end
              )
  end H.

Lemma whnormalize_type_of_whnf {n} (T: term n) H :
  whnf (whnormalize_type_of T H).
  destruct T; simpl; try apply whnormalize_SN_whnf. destruct s; try apply whnormalize_SN_whnf.
  repeat constructor.
Qed.

Lemma whnormalize_type_of_wstep_star {n} (T: term n) (H: exists Sc Γ t, Γ ⊢(Sc) t: T) :
  T w≻* whnormalize_type_of T H.
Proof.
  destruct T; try apply whnormalize_SN_wstep_star.
  destruct s; try apply whnormalize_SN_wstep_star. constructor.
Qed.

Lemma whnormalize_type_of_step_star {n} (T: term n) (H: exists Sc Γ t, Γ ⊢(Sc) t: T) :
  T ≻* whnormalize_type_of T H.
Proof.
  apply wstep_star_is_step_star, whnormalize_type_of_wstep_star.
Qed.

Lemma whnormalize_type_of_preserves {n} (T: term n) H :
  forall Sc Γ t, Γ ⊢(Sc) t : T -> Γ ⊢(Sc) t : whnormalize_type_of T H.
Proof.
  intros. apply srt_typing in H0 as H'. destruct H' as [| [s H']].
  - subst. simpl. assumption.
  - econstructor; try eassumption.
    + apply Requiv_clot_star, whnormalize_type_of_step_star.
    + eapply subject_reduction; try eassumption. apply whnormalize_type_of_step_star.
Qed.

Lemma neutral_not_redex {n} (t u: term n) : neutral t -> ¬ (t [≻] u).
  intro H. inversion 1; subst. inversion_clear H. inversion H1.
Qed.

Lemma neutral_step {n} (t u : term n) : neutral t -> t ≻ u -> neutral u.
Proof.
  induction 1 in u |- *; inversion 1; subst; destruct K; try discriminate; simpl in *;
    try solve [constructor]; subst; try solve [match goal with H: _ [≻] _ |- _ => inversion H end].
  - exfalso. eapply neutral_not_redex; [| eassumption]. constructor. assumption.
  - inversion H1; subst; clear H1. constructor. apply IHneutral. constructor. assumption.
  - inversion H1; subst; clear H1. constructor. assumption.
Qed.

Lemma neutral_step_plus {n} (t u : term n) : neutral t -> t ≻+ u -> neutral u.
Proof.
   induction 2; eapply neutral_step; eauto.
Qed.

Lemma neutral_step_star {n} (t u : term n) : neutral t -> t ≻* u -> neutral u.
Proof.
  destruct 2; eauto using neutral_step_plus.
Qed.

Lemma neutral_app_step {n} (t1 t2 u: term n) :
  neutral t1 -> App t1 t2 ≻ u -> exists u1 u2, u = App u1 u2.
Proof.
  inversion 2; subst. destruct K; simpl in *; try discriminate; eauto. subst. exfalso.
  eapply neutral_not_redex; [| eassumption]. constructor. assumption.
Qed.

Lemma neutral_app_step_star {n} (t1 t2 u: term n) :
  neutral t1 -> App t1 t2 ≻* u -> exists u1 u2, u = App u1 u2.
Proof.
  destruct 2; eauto. induction H0.
  - apply neutral_step_plus in H0; [| constructor; assumption]. clear H. firstorder subst.
    inversion_clear H0. eapply neutral_app_step; try eassumption.
  - eapply neutral_app_step; try eassumption.
Qed.

Lemma whnf_is_sort_type_or_never_will_be {n} {t: term n} :
  whnf t ->
  match t with Srt _ => True | _ => forall s, ¬ (t ≅ Srt s) end.
Proof.
  destruct t; auto; intros H ? e; apply Requiv_sym, srt_equiv in e.
  - apply var_star in e. discriminate.
  - apply pi_star in e. firstorder discriminate.
  - apply abs_star in e. firstorder discriminate.
  - inversion_clear H. inversion_clear H0. apply neutral_app_step_star in e; auto.
    firstorder discriminate.
Qed.

Lemma whnf_is_pi_type_or_never_will_be {n} {t: term n} :
  whnf t ->
  match t with Pi _ _ => True | _ => forall A B, ¬ (t ≅ Pi A B) end.
Proof.
  destruct t; auto; intros H ? ? e; apply Requiv_sym, pi_equiv in e as [A' [B' [eA [eB e]]]].
  - apply var_star in e. discriminate.
  - apply abs_star in e. firstorder discriminate.
  - inversion_clear H. inversion_clear H0. apply neutral_app_step_star in e; auto.
    firstorder discriminate.
  - apply srt_star in e. discriminate.
Qed.
