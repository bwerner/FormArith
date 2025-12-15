From Coq Require Import Utf8.
From Coq Require Import Arith Lia.
From FormArith Require Import Base.
From FormArith.LambdaCube Require Import Term Operational Typing.


Inductive SN {n : nat} (t : term n) : Prop :=
| SN_on : (∀ u, t ≻ u → SN u) → SN t.

(* The following is an attempt at formalizing the proof of normalization for CoC
   which can be found in Gilles Dowek's "Proofs in Theories" notes *)

Notation "'𝓟' X" := (X → Prop)
                      (at level 10,
                       left associativity).

Definition elem {X : Type} (x : X) (S : 𝓟 X) : Prop := S x.

Notation "x ∈ X" := (elem x X)
                      (at level 20,
                         no associativity).

Definition tset := ∀ (n : nat), 𝓟 (term n).

Definition sn : tset := λ n t, SN t.

Definition pi_set (X : tset) (S : 𝓟 tset) :=
  λ n (t : term n),
    SN t ∧
    ∀ ty bod tm Y,
       tm ∈ (X n) →
       Y ∈ S →
       t ≻* Abs ty bod →
       bind (bind_first tm) bod ∈ (Y n).

Definition tset_equiv (X Y : tset) : Prop :=
  ∀ n t, X n t ↔ Y n t.

Notation "X ≡ Y" := (tset_equiv X Y)
                      (at level 20,
                         no associativity
                      ).

Lemma tset_equiv_refl {X : tset} : X ≡ X.
Proof. firstorder. Qed.

Lemma tset_equiv_sym {X Y : tset} : X ≡ Y → Y ≡ X.
Proof. firstorder. Qed.

Lemma tset_equiv_trans {X Y Z : tset} : X ≡ Y → Y ≡ Z → X ≡ Z.
Proof.
  intros XY YZ n t.
  split.
  - intros Xt.
    apply YZ, XY, Xt.
  - intros Zt.
    apply XY, YZ, Zt.
Qed.

Definition inter (S : 𝓟 tset) : tset :=
  λ n t, ∀ Y, Y ∈ S → Y n t.

Notation "⋂ S" := (inter S)
                    (at level 10,
                       left associativity).

Inductive candidate : tset → Prop :=
| c_sn X : X ≡ sn → candidate X
| c_pi X S Z : Z ≡ pi_set X S →
               candidate X →
               (∀ Y, Y ∈ S → candidate Y) →
               candidate Z
| c_inter X S : X ≡ ⋂ S →
                (∀ Y, Y ∈ S → candidate Y) →
                candidate X.

Definition Cand : Prop := ∃ X, candidate X.

Definition cand_sn : Cand := ex_intro _ _ (c_sn _ tset_equiv_refl).

Inductive annot : Type :=
| sing : annot
| c : annot
| func : annot → annot → annot.

Lemma dec_eq_annot (x y : annot) : {x = y} + {x ≠ y}.
Proof.
  induction x in y |-*.
  - destruct y; [now left| right; discriminate..].
  - destruct y; [| now left |]; right; discriminate.
  - destruct y; [right; discriminate..|].
    destruct (IHx1 y1) as [-> | H].
    + destruct (IHx2 y2) as [-> | H]; [now left|].
      right.
      now injection.
    + right.
      now injection.
Qed.

Lemma annot_UIP {x y : annot} (p q : x = y) : p = q.
Proof.
  apply Eqdep_dec.UIP_dec, dec_eq_annot.
Qed.

Fixpoint M_annot {n} (t : term n) : annot :=
  match t with
  | Srt _ => c
  | Var _ => sing
  | Abs _ t => M_annot t
  | App t _ => M_annot t
  | Pi ty fam =>
      match M_annot fam with
      | sing => sing
      | ann_f =>
          match M_annot ty with
          | sing => ann_f
          | ann_ty => func ann_ty ann_f
          end
      end
  end.

Fixpoint M_annot_ctx {m n} (K : ctx m n) (a : annot) : annot :=
  match K with
  | Hole => a 
  | AbsL _ t => M_annot t
  | AbsR _ K => M_annot_ctx K a
  | AppL K _ => M_annot_ctx K a
  | AppR t _ => M_annot t
  | PiL K fam =>
      match M_annot fam with
      | sing => sing
      | ann_f =>
          match M_annot_ctx K a with
          | sing => ann_f
          | ann_ty => func ann_ty ann_f
          end
      end
  | PiR ty K =>
      match M_annot_ctx K a with
      | sing => sing
      | ann_f =>
          match M_annot ty with
          | sing => ann_f
          | ann_ty => func ann_ty ann_f
          end
      end
  end.

Fixpoint ann_interp (ann : annot) : Prop :=
  match ann with
  | c => Cand
  | sing => True
  | func ann_b ann_f => ann_interp ann_b → ann_interp ann_f
  end.

Definition M {n} (t : term n) : Prop := ann_interp (M_annot t).

Lemma M_annot_fill {m n} (t : term m) (K : ctx m n) :
  M_annot (fill K t) = M_annot_ctx K (M_annot t).
Proof.
  induction K; auto;
    simpl;
    now rewrite IHK.
Qed.

Lemma M_annot_object {Sc n} (Γ : typing_ctx n) (t A : term n) :
  Γ ⊢(Sc) A : Srt Star → Γ ⊢(Sc) t : A → M_annot t = sing.
Proof.
  induction 2; subst.
  - contradict H.
    clear.
    remember (Srt Box).
    induction 1; try discriminate; tauto.
  - reflexivity.
  - contradict H.
    clear.
    destruct s'; swap 1 2.
    { remember (Srt Box).
      induction 1; try discriminate; tauto.
    }
    intros C.
    apply typ_star_inv in C.
    apply srt_equiv_srt in C.
    discriminate.
  - simpl.
    apply IHtyping3.
    apply typ_pi_inv in H as (s1 & s2 & eq_star2 & typ_A & typ_B & pi_sc).
    apply srt_equiv_srt in eq_star2.
    subst.
    assumption.
  - simpl.
    apply IHtyping1.
    apply srt_typing in H0_ as [|[s' typ_piAB]]; [discriminate|].
    apply typ_pi_inv in typ_piAB as (s1 & s2 & eq_star2 & typ_A & typ_B & pi_sc).
    destruct s2; try solve [econstructor; eauto].
    pose proof (bind_first_typ H0_0 typ_B) as typ_B'.
    simpl in typ_B'.
    pose proof (unique_typing H typ_B').
    apply srt_equiv_srt in H0.
    discriminate.
  - apply IHtyping1.
    apply srt_typing in H0_ as [C | [s' typ_C]].
    + subst.
      apply srt_equiv in H0.
      pose proof (subject_reduction _ _ _ _ _ H H0) as C'.
      contradict C'.
      clear.
      remember (Srt Box).
      induction 1; try discriminate; tauto.
    + destruct s'; [assumption|].
      apply equiv_both_star in H0 as (v & red_A & red_B).
      pose proof (subject_reduction _ _ _ _ _ typ_C red_A) as Hv1.
      pose proof (subject_reduction _ _ _ _ _ H red_B) as Hv2.
      pose proof (unique_typing Hv1 Hv2) as C''.
      apply srt_equiv_srt in C''.
      discriminate.
Qed.

Lemma M_annot_type {Sc n} (Γ : typing_ctx n) (A B : term n) :
  Γ ⊢(Sc) B : Srt Box →
  Γ ⊢(Sc) A : B → M_annot A = sing.
Proof.
  induction 2; subst; try discriminate.
  - contradict H.
    clear.
    generalize (Srt (n := n) Box) at 2.
    intros B.
    remember (Srt Box).
    induction 1; try discriminate; tauto.
  - reflexivity.
  - destruct s'; swap 1 2.
    { contradict H.
      clear.
      generalize (Srt (n := n) Box) at 2.
      intros B.
      remember (Srt Box).
      induction 1; try discriminate; tauto.
    }
    simpl.
    rewrite IHtyping2; [reflexivity|].
    constructor.
    eapply typing_imp_ctx_wf.
    eassumption.
  - simpl.
    apply IHtyping3.
    apply typ_pi_inv in H as (s1 & s2 & eq_star2 & typ_A & typ_B & pi_sc).
    apply srt_equiv_srt in eq_star2 as <-.
    assumption.
  - simpl.
    apply IHtyping1.
    apply srt_typing in H0_ as [|[s typ_B]]; [discriminate|].
    apply typ_pi_inv in typ_B as (s1 & s2 & eq_star2 & typ_A & typ_B & pi_sc).
    clear dependent s.
    enough (s2 = Box).
    + subst.
      econstructor; eassumption.
    + eapply srt_equiv_srt, unique_typing; [|eassumption].
      eapply (bind_first_typ (T := Srt s2)); eassumption.
 - apply IHtyping1.
    apply srt_typing in H0_ as [C | [s' typ_C]].
    + subst.
      apply srt_equiv in H0.
      pose proof (subject_reduction _ _ _ _ _ H H0) as C'.
      contradict C'.
      clear.
      generalize (Srt (n := n) Box) at 2.
      intros B.
      remember (Srt Box).
      induction 1; try discriminate; tauto.
    + destruct s'; [|assumption].
      apply equiv_both_star in H0 as (v & red_A & red_B).
      pose proof (subject_reduction _ _ _ _ _ typ_C red_A) as Hv1.
      pose proof (subject_reduction _ _ _ _ _ H red_B) as Hv2.
      pose proof (unique_typing Hv1 Hv2) as C''.
      apply srt_equiv_srt in C''.
      discriminate.
Qed.

Lemma M_annot_typ_srt {Sc n} (Γ : typing_ctx n) (t A : term n) (s : sort):
  Γ ⊢(Sc) A : Srt s →
  Γ ⊢(Sc) t : A → M_annot t = sing.
Proof.
  destruct s.
  - apply M_annot_object.
  - apply M_annot_type.
Qed.

Lemma M_annot_ren {m} (t : term m) :
  ∀ n (σ : {i | i < m} → {i | i < n}),
  M_annot (ren σ t) = M_annot t.
Proof.
  induction t; simpl; trivial.
  intros k σ.
  rewrite IHt1, IHt2.
  reflexivity.
Qed.

Lemma M_annot_bind {m} (t : term m) :
  ∀ n (σ : {i | i < m} → term n),
  (∀ i, M_annot (σ i) = sing) →
  M_annot (bind σ t) = M_annot t.
Proof.
  induction t.
  - simpl. auto.
  - intros.
    simpl.
    rewrite IHt1, IHt2; trivial.
    intros i.
    unfold lift_bind.
    destruct (lt_dec _ _).
    + simpl.
      now rewrite M_annot_ren.
    + reflexivity.
  - intros.
    simpl.
    apply IHt2.
    unfold lift_bind.
    intros.
    destruct (lt_dec _ _).
    + simpl.
      now rewrite M_annot_ren.
    + reflexivity.
  - simpl. assumption.
  - trivial.
Qed.

Lemma M_annot_head_step {Sc n} (Γ : typing_ctx n) (t u A B : term n) :
  Γ ⊢(Sc) t : A →
  t [≻] u →
  M_annot t = M_annot u.
Proof.
  intros typ_t t_red.
  destruct t_red.
  simpl.
  apply typ_app_inv in typ_t as (C & D & A_eq_B & typ_abs & typ_arg).
  apply typ_abs_inv in typ_abs as (s1 & s2 & E & F & pi_eq & typ_ty & typ_E & typ_body & typ_pi & pi_sc).
  apply pi_equiv_pi in pi_eq as [C_eq D_eq].
  apply typ_pi_inv in typ_pi as (s3 & s4 & srt_eq & typ_C & typ_D & pi_sc').
  symmetry.
  apply M_annot_bind.
  intros i.
  unfold bind_first.
  destruct (lt_dec _ _); [reflexivity|].
  eapply M_annot_typ_srt; eassumption.
Qed.

Lemma M_annot_step {Sc n} (Γ : typing_ctx n) (t u A B : term n) :
  Γ ⊢(Sc) t : A →
  t ≻ u →
  M_annot t = M_annot u.
Proof.
  intros typ_t red_t.
  revert typ_t.
  destruct red_t as [m K t' u' red_t'].
  intros typ_Kt'.
  rewrite !M_annot_fill.
  f_equal.
  apply typed_imp_subterm_typed in typ_Kt' as (Γ' & A' & typ_t').
  eapply M_annot_head_step; eassumption.
Qed.

Lemma M_annot_red_plus {Sc n} (Γ : typing_ctx n) (t u A B : term n) :
  Γ ⊢(Sc) t : A →
  t ≻+ u →
  M_annot t = M_annot u.
Proof.
  intros typ_t red_t.
  induction red_t.
  - rewrite IHred_t.
    eapply M_annot_step; try eassumption.
    eapply subject_reduction; [|apply Rclot_plus_star; eassumption].
    eassumption.
  - eapply M_annot_step; eassumption.
Qed.

Lemma M_annot_red {Sc n} (Γ : typing_ctx n) (t u A B : term n) :
  Γ ⊢(Sc) t : A →
  t ≻* u →
  M_annot t = M_annot u.
Proof.
  intros typ_t red_t.
  destruct red_t.
  - reflexivity.
  - eapply M_annot_red_plus; eassumption.
Qed.

Lemma M_annot_equiv {Sc n} (Γ Δ : typing_ctx n) (t u A B : term n) :
  Γ ⊢(Sc) t : A →
  Δ ⊢(Sc) u : B →
  t ≅ u →
  M_annot t = M_annot u.
Proof.
  intros typ_t typ_u t_eq_u.
  apply equiv_both_star in t_eq_u as (v & red_t & red_u).
  transitivity (M_annot v);
    [|symmetry];
    eapply M_annot_red;
    eassumption.
Qed.

Lemma M_equiv {Sc n} (Γ Δ : typing_ctx n) (t u A B : term n) :
  Γ ⊢(Sc) t : A →
  Δ ⊢(Sc) u : B →
  t ≅ u →
  M t = M u.
Proof.
  intros.
  unfold M.
  f_equal.
  eapply M_annot_equiv;
    eassumption.
Qed.

Definition val (Sc : pi_scheme) {n} (Γ : typing_ctx n) :=
  ∀ (i : nat) (H : i < n), M (kth_index_ctx Γ i H).

Definition extend {Sc n} {Γ : typing_ctx n} {A} (Φ : val Sc Γ) (a : M A) : val Sc (Γ; A).
Proof.
  intros i H.
  simpl kth_index_ctx.
  unfold M. rewrite M_annot_ren.
  destruct (lt_dec i n) as [H1 | H1].
  - apply Φ.
  - assumption.
Defined.

Fixpoint denot
  Sc {n} (Γ : typing_ctx n)
  (t A : term n) (H : Γ ⊢(Sc) t : A)
  (Φ : val Sc Γ) {struct t}
  : M A.
Proof.
  destruct t.
  - apply typ_var_inv in H as A_eq_kth.
    assert (e : M_annot A = M_annot (kth_index_ctx Γ (proj1_sig s) (proj2_sig s))).
    {
      apply srt_typing in H as typ_A.
      apply typing_imp_ctx_wf in H.
      destruct typ_A as [contra|[s' typ_A]].
      + subst.
        apply srt_equiv in A_eq_kth.
        epose proof (wf_ctx_contains_types H) as [s' typ_kth].
        eapply subject_reduction in typ_kth; [|eassumption].
        contradict typ_kth.
        clear.
        remember (Srt Box) as B.
        induction 1; try discriminate; tauto.
      + epose proof (wf_ctx_contains_types H) as [s'' typ_kth].
        eapply M_annot_equiv; try eassumption.
    }
    unfold M.
    rewrite e.
    apply Φ.
  - apply typ_pi_inv in H as H1.
    destruct H1 as (s & s' & A_eq_s' & typ_t1 & typ_t2 & psc).
    assert (M_annot A = c).
    {
      destruct s'.
      - apply srt_typing in H as [contra|typ_A].
        { subst.
          now apply srt_equiv_srt in A_eq_s'.
        }
        destruct typ_A as [s0 typ_A].
        unshelve erewrite (M_annot_equiv _ _ _ _ _ _ _ ltac:(constructor) A_eq_s').
        5 : eassumption.
        1 : assumption.
        { eapply typing_imp_ctx_wf. eassumption. }
        reflexivity.
      - apply Requiv_sym, srt_equiv in A_eq_s'.
        apply srt_typing in H as [|[s0 typ_A]]; [now subst|].
        pose proof (subject_reduction _ _ _ _ _ typ_A A_eq_s') as C'.
        contradict C'.
        clear.
        remember (Srt Box).
        induction 1; try discriminate; tauto.
    }
    unfold M.
    rewrite H0.
    set (X := denot _ _ _ _ _ typ_t1 Φ).
    destruct X as [X cX].
    set (S := λ (Y : tset), ∃ c H, ex_intro _ Y H = denot Sc _ _ t2 _ typ_t2 (extend Φ c)).
    econstructor.
    unshelve eapply (c_pi _ S _ _ cX).
    { apply tset_equiv_refl. }
    intros Y HY.
    unfold S, elem in HY.
    now destruct HY as (c & cY & Y_eq).
  - apply typ_abs_inv in H as H1.
    destruct H1 as (s & s' & B & X & A_eq & typ_t1 & typ_B & typ_t2 & typ_1 & psc).
    unfold M.
    unshelve erewrite (M_annot_equiv _ Γ _ _ _ _ typ_1 _ A_eq).
    2 : {econstructor; eassumption. }
    simpl.
    assert (M_annot B = sing ∨ M_annot B ≠ sing) as [-> | ann_B].
    {
      destruct (M_annot B); [now left|right..]; discriminate.
    }
    { now simpl. }
    assert (M_annot t1 = sing ∨ M_annot t1 ≠ sing) as [ann_t1 | ann_t1].
    {
      destruct (M_annot t1); [now left|right..]; discriminate.
    }
    {
      assert (e : M t1).
      {
        unfold M.
        rewrite ann_t1.
        now simpl.
      }
      rewrite ann_t1.
      pose proof (v := denot _ _ _ _ _ typ_t2 (extend Φ e)).
      unfold M in v.
      now destruct (M_annot B) eqn:ann_B'.
    }
    pose proof (λ x, denot _ _ _ _ _ typ_t2 (extend Φ x)) as f.
    unfold M in f.
    destruct (M_annot B), (M_annot t1); try contradiction; assumption.
  - apply typ_app_inv in H as H1.
    destruct H1 as (A0 & B & A_eq & typ_t1 & typ_t2).
    apply srt_typing in typ_t1 as H2.
    destruct H2 as [|[s0 H2]]; [discriminate|].
    apply typ_pi_inv in H2 as H3.
    destruct H3 as (s & s' & srt_eq & typ_A0 & typ_B & psc).
    apply srt_equiv_srt in srt_eq as ->.
    assert (M_annot t2 = sing).
    {
      eapply M_annot_typ_srt; eassumption.
    }
    unfold M.
    replace (M_annot A) with (M_annot B); swap 1 2.
    {
      apply srt_typing in H as [-> | [s0 H1]].
      { eapply srt_equiv, subject_reduction in A_eq; swap 1 2.
        - eapply bind_first_typ; eassumption.
        - simpl in A_eq.
          contradict A_eq.
          clear.
          remember (Srt Box).
          induction 1; try discriminate; tauto.
      }
      unshelve erewrite (M_annot_equiv _ _ _ _ _ _ _ _ A_eq).
      7 : { eapply bind_first_typ; eassumption. }
      3 : { apply H1. }
      symmetry.
      apply M_annot_bind.
      intros i.
      unfold bind_first.
      now destruct (lt_dec _ _).
    }
    pose proof (denot _ _ _ _ _ typ_t1 Φ) as f.
    pose proof (denot _ _ _ _ _ typ_t2 Φ) as x.
    unfold M in f, x.
    simpl in f.
    assert (M_annot B = sing ∨ M_annot B ≠ sing) as [-> | ann_B].
    {
      destruct (M_annot B); [now left|right..]; discriminate.
    }
    { now simpl. }
    assert (M_annot A0 = sing ∨ M_annot A0 ≠ sing) as [ann_A0 | ann_A0].
    {
      destruct (M_annot A0); [now left|right..]; discriminate.
    }
    { rewrite ann_A0 in *.
      now destruct (M_annot B).
    }
    destruct (M_annot A0), (M_annot B); try contradiction; exact (f x).
  - destruct s.
    + apply srt_typing in H as H1.
      destruct H1 as [->|contra].
      { exact cand_sn. }
      destruct contra as [s0 H1].
      apply typ_star_inv, Requiv_sym, srt_equiv in H.
      eapply subject_reduction in H1; [|eassumption].
      contradict H1.
      clear.
      remember (Srt Box).
      induction 1; try discriminate; tauto.
    + contradict H.
      clear.
      remember (Srt Box).
      induction 1; try discriminate; tauto.
Defined.

Lemma denot_irrel
  Sc {n} (Γ : typing_ctx n)
  (t A : term n) (H1 H2 : Γ ⊢(Sc) t : A)
  (Φ : val Sc Γ) : denot _ _ _ _ H1 Φ = denot _ _ _ _ H2 Φ.
Proof.
  induction t; simpl.
  - f_equal.
    apply annot_UIP.
  - destruct (typ_pi_inv _ _ _ _ _), (typ_pi_inv _ _ _ _ _).
    destruct e, e0.
    destruct a, a0.
    destruct a, a0.
    destruct a, a0.
    f_equal.
    + assert (x = x0) as q.
      {
        eapply srt_equiv_srt, unique_typing; eassumption.
      }
      destruct q.
      assert (x1 = x2) as q.
      {
        eapply srt_equiv_srt, unique_typing; eassumption.
      }
      destruct q.
      rewrite (IHt1 _ _ t t0).
      destruct (denot _ _ _ _ _).
      unshelve eapply eq_ex_intro.
      * f_equal.
     (* Unfortunately this requires funext, stating a
        precise equivalence lemma might be too involved*)
Abort. 


Lemma typing_SN {Sc : pi_scheme} {n : nat} (Γ : typing_ctx n) (t A : term n) :
  Γ ⊢(Sc) t : A → SN t.
Admitted.
