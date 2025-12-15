From Coq Require Import Utf8.
From Coq Require Import Arith Lia.
From FormArith Require Import Base.
From FormArith.LambdaCube Require Import Term Operational Typing SN WHNF.

Fixpoint next_step {n} (t: term n) : option (term n) :=
  match t with
  | Var _ | Srt _ => None
  | Pi A B =>
      match next_step A with
      | Some A' => Some (Pi A' B)
      | None => match next_step B with
               | Some B' => Some (Pi A B')
               | None => None
               end
      end
  | Abs A t =>
      match next_step A with
      | Some A' => Some (Abs A' t)
      | None => match next_step t with
               | Some t' => Some (Abs A t')
               | None => None
               end
      end
  | App t u =>
      match next_step t with
      | Some t' => Some (App t' u)
      | None => match next_step u with
               | Some u' => Some (App t u')
               | None => match t with
                        | Abs _ f => Some (bind (bind_first u) f)
                        | _ => None
                        end
               end
      end
  end.

Lemma next_step_some {n} {t t' : term n} : next_step t = Some t' -> t ≻ t'.
Proof.
  induction t; simpl; try discriminate.
  all: destruct (next_step t1);
    [
      specialize (IHt1 _ eq_refl) |
      destruct (next_step t2); try discriminate; try specialize (IHt2 _ eq_refl)
    ]; intro e; inversion e; subst; clear e.
  - apply step_under_context with (K := PiL Hole t2). assumption.
  - apply step_under_context with (K := PiR t1 Hole). assumption.
  - apply step_under_context with (K := AbsL Hole t2). assumption.
  - apply step_under_context with (K := AbsR t1 Hole). assumption.
  - apply step_under_context with (K := AppL Hole t2). assumption.
  - apply step_under_context with (K := AppR t1 Hole). assumption.
  - rename H0 into e. destruct t1; try discriminate. inversion e; subst; clear e.
    apply ctx_red with (K := Hole). constructor.
Qed.

Lemma next_step_none {n} {t: term n} : next_step t = None -> forall t', ¬ (t ≻ t').
Proof.
  induction t; simpl in *; intros e t'.
  - apply no_var_step.
  - destruct (next_step t1); try discriminate. destruct (next_step t2); try discriminate.
    specialize (IHt1 eq_refl). specialize (IHt2 eq_refl).
    intro H. apply pi_step in H. firstorder.
  - destruct (next_step t1); try discriminate. destruct (next_step t2); try discriminate.
    specialize (IHt1 eq_refl). specialize (IHt2 eq_refl).
    intro H. apply abs_step in H. firstorder.
  - destruct (next_step t1); try discriminate. destruct (next_step t2); try discriminate.
    specialize (IHt1 eq_refl). specialize (IHt2 eq_refl).
    intro H. inversion H; subst. destruct K; simpl in *; try discriminate.
    + subst. inversion H1; subst; discriminate.
    + inversion H0; subst. eapply IHt1. constructor. eassumption.
    + inversion H0; subst. eapply IHt2. constructor. eassumption.
  - apply no_srt_step.
Qed.

Fixpoint normalize {n} (t: term n) (H: SN t) : term n :=
  match H with
  | SN_on _ H =>
      match next_step t as o return next_step t = o -> term n with
      | Some t' => fun e => normalize t' (H t' (next_step_some e))
      | None => fun _ => t
      end eq_refl
  end.

Fixpoint step_star_normalize {n} (t: term n) (H: SN t) : t ≻* normalize t H.
Proof.
  destruct H. simpl.
  generalize (@eq_refl _ (next_step t)).
  generalize (next_step t) at 2 3.
  destruct o.
  - intro. eapply Rstar_trans; swap 1 2.
    + apply step_star_normalize.
    + do 2 constructor. apply next_step_some. assumption.
  - constructor.
Qed.

Fixpoint normalize_normal_form {n} (t t': term n) (H: SN t) : ¬ normalize t H ≻ t'.
Proof.
  destruct H. simpl. generalize (@eq_refl _ (next_step t)). generalize (next_step t) at 2 3.
  destruct o.
  - intro. apply normalize_normal_form.
  - intro. apply next_step_none. assumption.
Qed.

Lemma all_step_star_normalize {n} (t t': term n) (H: SN t) : t ≻* t' -> t' ≻* normalize t H.
Proof.
  intro rleft. pose proof (rright := step_star_normalize t H).
  destruct (confluence_step rleft rright) as [v [Hres rnorm]].
  enough (v = normalize t H) by (subst; assumption). destruct rnorm as [|? rnorm]; auto.
  exfalso. revert rnorm. clear. induction 1; eauto using normalize_normal_form.
  eapply normalize_normal_form; eassumption.
Qed.

Lemma equiv_same_normal_form {n} (t t': term n) (H: SN t) (H' : SN t') :
  t ≅ t' -> normalize t H = normalize t' H'.
  intro Hcong. apply equiv_both_star in Hcong as [v [rt rt']].
  assert (rt't : t' ≻* normalize t H).
  - eapply Rstar_trans; try eassumption. eapply all_step_star_normalize. assumption.
  - apply all_step_star_normalize with (H := H') in rt't as [|? rnorm]; auto.
    exfalso. revert rnorm. clear. induction 1; eauto. eapply normalize_normal_form; eassumption.
Qed.

Fixpoint term_eqb {n} (t t' : term n) : bool :=
  match t, t' with
  | Var k, Var k' => Nat.eqb (proj1_sig k) (proj1_sig k')
  | Abs A t, Abs B u => term_eqb A B && term_eqb t u
  | Srt Star, Srt Star | Srt Box, Srt Box => true
  | Pi A B, Pi A' B' => term_eqb A A' && term_eqb B B'
  | App t u, App t' u' => term_eqb t t' && term_eqb u u'
  | _, _ => false
  end.

Lemma term_eqb_true_iff {n} (t t': term n) : term_eqb t t' = true <-> t = t'.
Proof.
  split.
  - induction t in t' |- *; destruct t'; simpl;
      do 2 match goal with |- match ?s with _ => _ end = _ -> _ => destruct s | _ => idtac end;
      try discriminate; try reflexivity; intro e; try apply andb_prop in e; f_equal;
      intuition auto.
    apply sig_lt_ext. apply Nat.eqb_eq. assumption.
  - induction t in t' |- *; destruct t'; simpl; inversion 1; subst;
      do 2 match goal with |- match ?s with _ => _ end = _ => destruct s | _ => idtac end;
    try specialize (IHt1 _ eq_refl); try specialize (IHt2 _ eq_refl); eauto using andb_true_intro.
    apply Nat.eqb_refl.
Qed.

Lemma term_eqb_true {n} (t t': term n) : term_eqb t t' = true -> t = t'.
  apply term_eqb_true_iff.
Qed.

Lemma term_eqb_false_iff {n} (t t': term n) : term_eqb t t' = false <-> t <> t'.
Proof.
  split.
  - intros H e. apply term_eqb_true_iff in e. congruence.
  - intros H. destruct (term_eqb _ _) eqn : e; auto. apply term_eqb_true in e. tauto.
Qed.

Lemma term_eqb_false {n} (t t': term n) : term_eqb t t' = false -> t <> t'.
  apply term_eqb_false_iff.
Qed.

Definition term_eq_dec {n} (t t': term n) : {t = t'} + {t <> t'}.
  destruct (term_eqb t t') eqn: e.
  - left. apply term_eqb_true. assumption.
  - right. apply term_eqb_false. assumption.
Defined.

Definition convertible {n} (t t': term n) (H: SN t) (H': SN t') : bool :=
  term_eqb (normalize t H) (normalize t' H').

Lemma convertible_true_iff {n} (t t': term n) (H: SN t) (H': SN t') :
  convertible t t' H H' = true <-> t ≅ t'.
Proof.
  split.
  - intro e. apply term_eqb_true in e. eapply Requiv_trans.
    + apply Requiv_clot_star. apply step_star_normalize.
    + rewrite e. apply Requiv_clot_star_r. apply step_star_normalize.
  - intro. apply term_eqb_true_iff. apply equiv_same_normal_form. assumption.
Qed.

Lemma convertible_true {n} (t t': term n) (H: SN t) (H': SN t') :
  convertible t t' H H' = true -> t ≅ t'.
  apply convertible_true_iff.
Qed.

Lemma convertible_false_iff {n} (t t': term n) (H: SN t) (H': SN t') :
  convertible t t' H H' = false <-> ¬ t ≅ t'.
Proof.
  split.
  - intros e Heq. apply convertible_true_iff with (H := H) (H' := H') in Heq. congruence.
  - intro. destruct (convertible _ _ _ _) eqn: e; try reflexivity.
    apply convertible_true in e. tauto.
Qed.

Lemma convertible_false {n} (t t': term n) (H: SN t) (H': SN t') :
  convertible t t' H H' = false -> ¬ t ≅ t'.
  apply convertible_false_iff.
Qed.

Definition convertible_dec {n} (t t': term n) (H: SN t) (H': SN t') : {t ≅ t'} + {¬ t ≅ t'} :=
  (if convertible t t' H H' as b return convertible t t' H H' = b -> _
   then fun e => left (convertible_true _ _ _ _ e)
   else fun e => right (convertible_false _ _ _ _ e)
  ) eq_refl.
  
Definition convertible_typed {Sc} {n} {Γ Γ'} {t t': term n}
  (H : exists T, Γ ⊢(Sc) t : T) (H' : exists T', Γ' ⊢(Sc) t' : T') :
  {t ≅ t'} + {¬ t ≅ t'} :=
  convertible_dec t t'
    (let (T, H) := H in typing_SN _ _ _ H)
    (let (T', H') := H' in typing_SN _ _ _ H').
