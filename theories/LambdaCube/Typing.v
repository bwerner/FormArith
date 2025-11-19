From Coq Require Import Utf8.
From Coq Require Import Arith Lia.
From FormArith Require Import Base.
From FormArith.LambdaCube Require Import Term Operational.

Inductive typing_ctx : nat -> Type :=
| empty : typing_ctx 0
| cons {n} : typing_ctx n -> term n -> typing_ctx (S n).

Notation "\" := empty.
Notation "A , t" := (cons A t) (at level 61, left associativity, t at next level).

Search (_ < S _ -> {_} + {_}).

Fixpoint kth_index_ctx {n} (Γ: typing_ctx n) k {struct Γ} : k < n -> term n :=
  match Γ in typing_ctx n return k < n -> term n with
  | \ => fun H => match Nat.nlt_0_r _ H with end
  | @cons n Γ t =>
      fun _ =>
        ren weaken
          match lt_dec k n with
          | left H => kth_index_ctx Γ k H
          | right _ => t
          end
  end.

Definition pi_scheme := sort -> sort -> bool.

Definition pi_scheme_check (P: pi_scheme) (s s': sort) : Prop := P s s' = true.

Reserved Notation "A ⊢( P ) s ':' t"
  (at level 70, s at next level, t at next level, P at next level).
Reserved Notation "A ⊢( P )" (at level 70, P at next level).

Inductive typing (P: pi_scheme) : forall {n}, typing_ctx n -> term n -> term n -> Prop :=
| typ_star {n} {Γ: typing_ctx n} : Γ ⊢(P) -> Γ ⊢(P) Srt Star : Srt Box
| typ_var {n} {Γ: typing_ctx n} {i} :
  Γ ⊢(P) -> Γ ⊢(P) Var i : kth_index_ctx Γ (proj1_sig i) (proj2_sig i)
| typ_pi {n} {Γ: typing_ctx n} {A B s s'} :
  pi_scheme_check P s s' -> Γ ⊢(P) A : Srt s -> Γ, A ⊢(P) B : Srt s' -> Γ ⊢(P) Pi A B : Srt s'
| typ_abs {n} {Γ: typing_ctx n} {A B s s' t} :
  pi_scheme_check P s s' ->
  Γ ⊢(P) A : Srt s ->
  Γ, A ⊢(P) B : Srt s' ->
  Γ, A ⊢(P) t : B ->
  Γ ⊢(P) Abs A t : Pi A B
| typ_app {n} {Γ: typing_ctx n} {A B t u} :
  Γ ⊢(P) t : Pi A B -> Γ ⊢(P) u : A -> Γ ⊢(P) App t u : bind (bind_first u) B
| typ_conv {n} {Γ: typing_ctx n} {t A B} :
  Γ ⊢(P) t : A -> A ≅ B -> Γ ⊢(P) t : B
with ctx_wf (P: pi_scheme) : forall {n}, typing_ctx n -> Prop :=
| empty_wf : \ ⊢(P)
| cons_wf {n} {A: typing_ctx n} {t: term n} {s} :
  A ⊢(P) -> A ⊢(P) t : Srt s -> A, t ⊢(P)
where "A ⊢( P ) t ':' s" := (typing P A t s)
and "A ⊢( P )" := (ctx_wf P A)
.

Definition is_star (s: sort) : bool :=
  match s with Star => true | Box => false end.

Definition is_box (s: sort) : bool :=
  match s with Star => false | Box => true end.

Open Scope bool.

Definition simple_typed : pi_scheme :=
  fun s s' => is_star s && is_star s'.

Notation "'λ→'" := simple_typed.

Definition systemF : pi_scheme :=
  fun s s' => is_star s'.

Notation "'F'" := systemF.

Definition weak_omega : pi_scheme :=
  fun s s' => (is_star s && is_star s') || (is_box s && is_box s').

Notation "'wω'" := weak_omega.

Definition systemP : pi_scheme :=
  fun s s' => is_star s.

Notation "'P'" := systemP.

Definition system_omega : pi_scheme :=
  fun s s' => is_box s || is_star s'.

Definition systemPF : pi_scheme :=
  fun s s' => is_star s || is_star s'.

Notation "'PF'" := systemPF.

Definition P_weak_omega : pi_scheme :=
  fun s s' => is_star s || is_box s'.

Notation "'Pwω'" := P_weak_omega.

Definition CoC : pi_scheme :=
  fun s s' => true.

Notation "'C'" := CoC.

Lemma typ_star_inv Sc {n} (Γ : typing_ctx n) t : Γ ⊢(Sc) Srt Star : t -> t ≅ Srt Box.
Proof.
  remember (Srt Star). induction 1; try discriminate; try solve [constructor].
  intuition subst. eapply Requiv_trans; try eassumption. apply Requiv_sym. assumption.
Qed.

Lemma typ_var_inv Sc {n} (Γ : typing_ctx n) i T :
  (Γ ⊢(Sc) Var i : T) -> T ≅ kth_index_ctx Γ (proj1_sig i) (proj2_sig i).
  remember (Var i). induction 1 in i, Heqt |- *; try discriminate.
  - inversion Heqt. subst. constructor.
  - subst. specialize (IHtyping _ eq_refl). eapply Requiv_trans; eauto using Requiv_sym.
Qed.

Lemma typ_pi_inv Sc {n} (Γ : typing_ctx n) A B T :
  Γ ⊢(Sc) Pi A B : T -> exists s s',
        T ≅ Srt s' /\ Γ ⊢(Sc) A : Srt s /\ Γ, A ⊢(Sc) B : Srt s' /\ pi_scheme_check Sc s s'.
Proof.
  remember (Pi A B). induction 1 in A, B, Heqt |- *; try discriminate.
  - exists s. exists s'. inversion Heqt; subst; clear Heqt. intuition constructor.
  - subst. specialize (IHtyping _ _ eq_refl). destruct IHtyping as [s [s']].
    exists s. exists s'. intuition. eauto using Requiv_trans, Requiv_sym.
Qed.

Lemma typ_abs_inv Sc {n} (Γ: typing_ctx n) A t T :
  Γ ⊢(Sc) Abs A t : T ->
  exists s s' B,
    T ≅ Pi A B /\ Γ ⊢(Sc) A : Srt s /\ Γ, A ⊢(Sc) B : Srt s' /\ Γ, A ⊢(Sc) t : B /\
      pi_scheme_check Sc s s'.
Proof.
  remember (Abs A t).
  induction 1 in A, t, Heqt0 |- *; try discriminate.
  - clear IHtyping1 IHtyping2 IHtyping3. inversion Heqt0. subst. clear Heqt0.
    exists s. exists s'. exists B. intuition constructor.
  - subst. specialize (IHtyping A t eq_refl).
    destruct IHtyping as [s [s' [B0]]].
    exists s. exists s'. exists B0. intuition eauto using Requiv_trans, Requiv_sym.
Qed.

Lemma typ_app_inv Sc {n} (Γ: typing_ctx n) t u T :
  Γ ⊢(Sc) App t u : T -> exists A B, T ≅ bind (bind_first u) B /\ Γ ⊢(Sc) t : Pi A B /\ Γ ⊢(Sc) u : A.
Proof.
  remember (App t u) as t0.
  induction 1 in t, u, Heqt0 |- *; try discriminate.
  - clear IHtyping1 IHtyping2. exists A, B. inversion Heqt0; subst; clear Heqt0. intuition constructor.
  - subst. specialize (IHtyping _ _ eq_refl).
    destruct IHtyping as [A0 [B0]].
    exists A0, B0. intuition eauto using Requiv_trans, Requiv_sym.
Qed.

Lemma typing_imp_ctx_wf Sc {n} (Γ: typing_ctx n) t s : Γ ⊢(Sc) t : s -> Γ ⊢(Sc).
Proof.
  induction 1; try assumption.
Qed.

Lemma equiv_context (Sc : pi_scheme) {n} (Γ Γ': typing_ctx n) t s :
  (forall k H, kth_index_ctx Γ' k H ≅ kth_index_ctx Γ k H) -> Γ' ⊢(Sc) -> Γ ⊢(Sc) t : s -> Γ' ⊢(Sc) t : s.
Proof.
  intros H pr. induction 1.
  - constructor. assumption.
  - econstructor; swap 1 2. { apply H. } constructor. assumption.
  - econstructor; try eassumption; auto.
    apply IHtyping2.
    + intros. simpl. destruct (lt_dec k n); try solve [constructor].
      apply ren_preserves_step_equiv. auto.
    + econstructor; try eassumption.
      apply IHtyping1; assumption.
  - econstructor; try eassumption; auto.
    + apply IHtyping2.
      * intros. simpl. destruct (lt_dec k n); try solve [constructor].
        apply ren_preserves_step_equiv. auto.
      * econstructor; try eassumption.
        apply IHtyping1; assumption.
    + apply IHtyping3.
      * intros. simpl. destruct (lt_dec k n); try solve [constructor].
        apply ren_preserves_step_equiv. auto.
      * econstructor; try assumption. apply IHtyping1; assumption.
  - econstructor; auto.
  - econstructor; eauto.
Qed.

Lemma weakening {Sc n k} {σ: {i | i < n} -> {i | i < k}} {Γ Γ' x T}  :
  (forall i,
      ren σ (kth_index_ctx Γ (proj1_sig i) (proj2_sig i)) =
        kth_index_ctx Γ' (proj1_sig (σ i)) (proj2_sig (σ i))) ->
  Γ ⊢(Sc) x : T -> Γ' ⊢(Sc) -> Γ' ⊢(Sc) ren σ x : ren σ T.
  intro H. induction 1 in k, σ, Γ', H |- *; simpl; intro.
  - constructor. assumption.
  - rewrite H. constructor. assumption.
  - econstructor; try eassumption.
    + apply IHtyping1; try assumption.
    + apply IHtyping2; try assumption.
      * intro. unfold lift at 2 3. destruct (lt_dec (proj1_sig i) n); simpl.
        -- rewrite ren_comp. destruct (lt_dec _ _); try tauto.
           epose proof (proj2_sig (σ (exist _ (proj1_sig i) l))). simpl in *.
           destruct (lt_dec _ _); try tauto.
           replace l1 with (proj2_sig (σ (exist _ (proj1_sig i) l))) by apply le_unique.
           rewrite <- H. rewrite ren_comp. simpl. replace l with l0 by apply le_unique.
           apply ren_ext, lift_weaken.
        -- destruct (lt_dec _ _); try tauto. rewrite ren_comp. destruct (lt_dec _ _); try lia.
           rewrite ren_comp. apply ren_ext, lift_weaken.
      * econstructor; try assumption. apply IHtyping1; assumption.
  - econstructor; try eassumption.
    + apply IHtyping1; assumption.
    + apply IHtyping2.
      * intro. unfold lift at 2 3. destruct (lt_dec (proj1_sig i) n); simpl.
        -- rewrite ren_comp. destruct (lt_dec _ _); try tauto.
           epose proof (proj2_sig (σ (exist _ (proj1_sig i) l))). simpl in *.
           destruct (lt_dec _ _); try tauto.
           replace l1 with (proj2_sig (σ (exist _ (proj1_sig i) l))) by apply le_unique.
           rewrite <- H. rewrite ren_comp. simpl. replace l with l0 by apply le_unique.
           apply ren_ext, lift_weaken.
        -- destruct (lt_dec _ _); try tauto. rewrite ren_comp. destruct (lt_dec _ _); try lia.
           rewrite ren_comp. apply ren_ext, lift_weaken.
      * econstructor; eauto.
    + apply IHtyping3.
      * intro. unfold lift at 2 3. destruct (lt_dec (proj1_sig i) n); simpl.
        -- rewrite ren_comp. destruct (lt_dec _ _); try tauto.
           epose proof (proj2_sig (σ (exist _ (proj1_sig i) l))). simpl in *.
           destruct (lt_dec _ _); try tauto.
           replace l1 with (proj2_sig (σ (exist _ (proj1_sig i) l))) by apply le_unique.
           rewrite <- H. rewrite ren_comp. simpl. replace l with l0 by apply le_unique.
           apply ren_ext, lift_weaken.
        -- destruct (lt_dec _ _); try tauto. rewrite ren_comp. destruct (lt_dec _ _); try lia.
           rewrite ren_comp. apply ren_ext, lift_weaken.
      * econstructor; eauto.
  - simpl in *. rewrite ren_bind.
    replace (bind (ren σ ∘ bind_first u) B) with (bind (bind_first (ren σ u)) (ren (lift σ) B)).
    + econstructor; eauto.
    + rewrite bind_ren. apply bind_ext. intro. unfold lift, bind_first. simpl.
      destruct (lt_dec _ n).
      * simpl. pose proof (proj2_sig (σ (exist _ (proj1_sig i) l))). simpl in *.
        destruct (lt_dec _ _); try tauto. f_equal. apply sig_lt_ext. reflexivity.
      * simpl. destruct (lt_dec _ _); try lia. reflexivity.
  - econstructor.
    + apply IHtyping; assumption.
    + apply ren_preserves_step_equiv. assumption.
Qed.

Lemma preservation (Sc: pi_scheme) {n} Γ (t u : term n) A :
  Γ ⊢(Sc) t : A -> t ≻ u -> Γ ⊢(Sc) u : A.
Proof.
  induction 1; intro red; inversion red; clear red;
    match goal with H : fill ?K _ = _ _ |- _ => (destruct K; simpl in *; try discriminate;
    subst; try solve [ match goal with H : _ [≻] _ |- _ => inversion H end ]) | _ => idtac end.
  - inversion H2; subst; clear H2. econstructor; try eassumption.
    + apply IHtyping1. constructor. assumption.
    + eapply equiv_context; try eassumption.
      * simpl. intros. destruct (lt_dec _ _); try solve [constructor].
        apply ren_preserves_step_equiv. apply Requiv_clot_r. constructor. assumption.
      * econstructor; try eauto. { eapply typing_imp_ctx_wf. eassumption. } apply IHtyping1.
        constructor. assumption.
  - inversion H2; subst; clear H2. econstructor; try eassumption.
    apply IHtyping2. constructor. assumption.
  - inversion H3; subst; clear H3. unshelve econstructor. { exact (Pi (fill K u0) B). }
    + econstructor; try eauto.
      * apply IHtyping1. constructor. assumption.
      * eapply equiv_context; try eassumption.
        -- simpl. intros. destruct (lt_dec _ _); try solve [constructor].
           apply ren_preserves_step_equiv, Requiv_clot_r. constructor. assumption.
        -- econstructor.
           ++ eapply typing_imp_ctx_wf; eassumption.
           ++ apply IHtyping1. constructor. assumption.
      * eapply equiv_context; try eassumption.
        -- simpl. intros. destruct (lt_dec _ _); try solve [constructor].
           apply ren_preserves_step_equiv, Requiv_clot_r. constructor. assumption.
        -- econstructor.
           ++ eapply typing_imp_ctx_wf; eassumption.
           ++ apply IHtyping1. constructor. assumption.
    + apply Requiv_clot_r. change (Pi (fill K ?x) B) with (fill (PiL K B) x). constructor.
      assumption.
  - inversion H3; subst; clear H3. econstructor; try eassumption.
    apply IHtyping3. constructor. assumption.
  - inversion H2; subst; clear H2. clear IHtyping1 IHtyping2.
    rename u0 into u.
    apply typ_abs_inv in H. destruct H as [s [s' [B0 H]]].
    destruct H as [Hequiv [type_ty [type_B0 [type_body pi_check]]]].
    apply pi_equiv_pi in Hequiv as [Aequiv Bequiv].
    assert (true_type_body : Γ, ty ⊢(Sc) body : B).
    { econstructor; eauto using Requiv_sym. }
    assert (true_type_u : Γ ⊢(Sc) u : ty).
    { econstructor; eauto. }
    revert true_type_body true_type_u. clear. intros tybody tyu.
    enough (
        forall n k (σ : {i | i < k} -> term n) Γ Γ' x T,
          (forall i, Γ ⊢(Sc) σ i : bind σ (kth_index_ctx Γ' (proj1_sig i) (proj2_sig i))) ->
          Γ' ⊢(Sc) x : T -> Γ ⊢(Sc) -> Γ ⊢(Sc) bind σ x : bind σ T).
    { eapply H; eauto using typing_imp_ctx_wf.
      intro. destruct i; simpl. unfold bind_first at 1. simpl. destruct (lt_dec _ _).
      - rewrite bind_ren. rewrite bind_id.
        + constructor. eapply typing_imp_ctx_wf; eassumption.
        + unfold bind_first, weaken. simpl. intro i. pose proof (proj2_sig i). simpl in *.
          destruct (lt_dec _ _); try tauto. f_equal. apply sig_lt_ext. reflexivity.
      - rewrite bind_ren. rewrite bind_id; try assumption.
        unfold bind_first, weaken. simpl. intro i. pose proof (proj2_sig i). simpl in *.
        destruct (lt_dec _ _); try tauto. f_equal. apply sig_lt_ext. reflexivity.
    }
    clear. intros ? ? ? ? ? ? ? H tyx Γwf. induction tyx in n, σ, Γ, H, Γwf |- *; simpl in *; auto.
    + constructor. assumption.
    + econstructor; eauto. eapply IHtyx2.
      * intro. unfold lift_bind at 1. destruct (lt_dec _ _).
        -- rewrite bind_weaken. eapply weakening.
           ++ intro. simpl. pose proof (proj2_sig i0). destruct (lt_dec _ _); try tauto.
              f_equal. f_equal. apply le_unique.
           ++ apply H.
           ++ econstructor; eauto.
        -- rewrite bind_weaken.
           replace (ren weaken (bind σ A)) with
             (kth_index_ctx (Γ, bind σ A) n (Nat.lt_succ_diag_r n)).
           ++ constructor. econstructor; eauto.
           ++ simpl. destruct (lt_dec n n); try lia. reflexivity.
      * econstructor; eauto.
    + econstructor; eauto.
      * apply IHtyx2.
        -- intro. rewrite bind_weaken. unfold lift_bind.
           destruct (lt_dec _ _).
           ++ eapply weakening; eauto.
              ** intro. simpl. pose proof (proj2_sig i0). simpl in *.
                 destruct (lt_dec _ _); try tauto. f_equal. f_equal. apply le_unique.
              ** econstructor; eauto.
           ++ replace (ren weaken (bind σ A)) with
                (kth_index_ctx (Γ, bind σ A) n (Nat.lt_succ_diag_r n)).
              ** do 2 econstructor; eauto.
              ** simpl. destruct (lt_dec _ _); try lia. reflexivity.
        -- econstructor; eauto.
      * apply IHtyx3.
        -- intro. rewrite bind_weaken. unfold lift_bind at 1. destruct (lt_dec _ _).
           ++ eapply weakening; eauto.
              ** intro. simpl. pose proof (proj2_sig i0). simpl in *.
                 destruct (lt_dec _ _); try tauto. f_equal. f_equal. apply le_unique.
              ** econstructor; eauto.
           ++ replace (ren weaken (bind σ A)) with
                (kth_index_ctx (Γ, bind σ A) n (Nat.lt_succ_diag_r n)).
              ** do 2 econstructor; eauto.
              ** simpl. destruct (lt_dec _ _); try lia. reflexivity.
        -- econstructor; eauto.
    + rewrite bind_comp. replace (bind (bind σ ∘ bind_first u) B) with
        (bind (bind_first (bind σ u)) (bind (lift_bind σ) B)).
      * econstructor; eauto.
      * rewrite bind_comp. apply bind_ext. intro. unfold lift_bind, bind_first at 2.
        destruct (lt_dec _ _); simpl.
        -- rewrite bind_ren. apply bind_id. intro. unfold weaken, bind_first. simpl.
           pose proof (proj2_sig k). simpl in *. destruct (lt_dec _ _); try tauto.
           f_equal. apply sig_lt_ext. reflexivity.
        -- unfold bind_first. simpl. destruct (lt_dec _ _); try lia. reflexivity.
    + econstructor; eauto. apply bind_preserves_step_equiv. assumption.
  - inversion H1; subst; clear H1. econstructor; try eassumption.
    apply IHtyping1. constructor. assumption.
  - inversion H1; subst; clear H1. econstructor.
    + econstructor; try eassumption. apply IHtyping2. constructor. assumption.
    + apply bind_preserves_step_equiv_in_subs. intro. unfold bind_first.
      destruct (lt_dec _ _).
      * constructor.
      * apply Requiv_clot_r. constructor. assumption.
  - subst. econstructor; try eassumption. apply IHtyping. constructor. assumption.
Qed.

Lemma subject_reduction (Sc: pi_scheme) {n} Γ (t u : term n) A :
  Γ ⊢(Sc) t : A -> t ≻* u -> Γ ⊢(Sc) u : A.
Proof.
  destruct 2; auto.
  induction H0; eapply preservation; eauto.
Qed.
