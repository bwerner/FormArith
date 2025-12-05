From Coq Require Import Utf8.
From Coq Require Import Arith Lia.
From FormArith Require Import Base.
From FormArith.LambdaCube Require Import Term Operational Typing SN whnf normalize.

Inductive strong_ctx_wf (Sc: pi_scheme) : forall {n}, typing_ctx n -> Type :=
| strong_empty_wf : strong_ctx_wf Sc \
| strong_cons_wf {n} {Γ: typing_ctx n} {A: term n} s :
  strong_ctx_wf Sc Γ -> Γ ⊢(Sc) A : Srt s -> strong_ctx_wf Sc (Γ; A)
.

Lemma strong_to_weak_ctx_wf Sc {n} (Γ: typing_ctx n) : strong_ctx_wf Sc Γ -> Γ ⊢(Sc).
Proof.
  induction 1; econstructor; eassumption.
Qed.

Fixpoint kth_srt_ctx {Sc} {n} {Γ: typing_ctx n} (H: strong_ctx_wf Sc Γ) (k: nat) {struct H}
  : k < n -> sort :=
  match H with
  | strong_empty_wf _ => fun H => match Nat.nlt_0_r k H with end
  | @strong_cons_wf _ n _ _ s H _ =>
      fun _ =>
        match lt_dec k n with
        | left l => kth_srt_ctx H k l
        | right _ => s
        end
  end.

Lemma kth_typ_index {Sc} {n} {Γ: typing_ctx n} (H: strong_ctx_wf Sc Γ) k (l : k < n) :
  Γ ⊢(Sc) kth_index_ctx Γ k l : Srt (kth_srt_ctx H k l).
Proof.
  induction H; simpl. { destruct (Nat.nlt_0_r _ _). } destruct (lt_dec _ _).
  - change (@Srt (S ?n) ?s) with (ren weaken (@Srt n s)). eapply weakening; eauto.
  - change (@Srt (S ?n) ?s) with (ren weaken (@Srt n s)). eapply weakening; eassumption.
Qed.

Lemma SN_srt {n} s : SN (@Srt n s).
Proof.
  constructor. intros. exfalso. eapply no_srt_step. eassumption.
Qed.

Inductive infer_ret Sc {n} Γ (t: term n) : Type :=
| Untyped
| Kind (typt: Γ ⊢(Sc) t : Srt Box)
| Sorted T s (typt: Γ ⊢(Sc) t : T) (typT: Γ ⊢(Sc) T : Srt s).

Arguments Kind {_ _ _ _}.
Arguments Sorted {_ _ _ _}.

(* Sorted means we have a term that is neither a type nor a kind, along with its sort *)

Fixpoint infer_aux Sc {n} {Γ} (H: strong_ctx_wf Sc Γ) (t: term n) {struct t}
  : infer_ret Sc Γ t :=
  match t with
  | Srt Star => Kind (typ_star _ (strong_to_weak_ctx_wf _ _ H))
  | Srt Box => Untyped _ _ _
  | Var k =>
      (*match kth_index_ctx Γ (proj1_sig k) (proj2_sig k)
            as T return
            Γ ⊢(Sc) Var k : T ->
                            Γ ⊢(Sc) T : Srt (kth_srt_ctx H (proj1_sig k) (proj2_sig k)) -> _
      with
      | Srt Star => fun H _ => _
      | T => fun typV typT => Sorted T _ typV typT
      end*) Sorted _ _ (typ_var _ (strong_to_weak_ctx_wf _ _ H)) (kth_typ_index H _ _)
  | Pi A B =>
      match infer_aux Sc H A with
      | Kind typA =>
          match infer_aux Sc (strong_cons_wf _ _ H typA) B with
          | Kind typB =>
              (if Sc Box Box as b return Sc Box Box = b -> _
               then fun e => Kind (typ_pi _ e typA typB)
               else fun _ => Untyped _ _ _) eq_refl
          | Sorted T s' typB typT =>
              let H' := ex_intro _ _ (ex_intro _ _ (ex_intro _ _ typT)) in
              match whnormalize_typed T H' as T' return Γ; A ⊢(Sc) B : T' -> _
              with
              | Srt Star =>
                  fun typB =>
                    (if Sc Box Star as b return Sc Box Star = b -> _
                     then fun e =>
                            Sorted _ _ (typ_pi _ e typA typB)
                               (typ_star _ (strong_to_weak_ctx_wf _ _ H))
                     else fun _ => Untyped _ _ _) eq_refl
              | _ => fun _ => Untyped _ _ _
              end (
                  let H' : T ≻* whnormalize_typed T H' := whnormalize_typed_step_star _ _ in
                  typ_conv _ typB (Requiv_clot_star H') (subject_reduction _ _ _ _ _ typT H')
                )
          | _ => Untyped _ _ _
          end
      | Sorted T s typA typT =>
          let H' := ex_intro _ _ (ex_intro _ _ (ex_intro _ _ typT)) in
          match whnormalize_typed T H' as T' return Γ ⊢(Sc) A : T' -> _
          with
          | Srt Star =>
              fun typA =>
                match infer_aux Sc (strong_cons_wf _ _ H typA) B with
                | Kind typB =>
                    (if Sc Star Box as b return Sc Star Box = b -> _
                     then fun e => Kind (typ_pi _ e typA typB)
                     else fun _ => Untyped _ _ _) eq_refl
                | Sorted T s' typB typT =>
                    let H' := ex_intro _ _ (ex_intro _ _ (ex_intro _ _ typT)) in
                    match whnormalize_typed T H' as T' return Γ; A ⊢(Sc) B : T' -> _
                    with
                    | Srt Star =>
                        fun typB =>
                          (if Sc Star Star as b return Sc Star Star = b -> _
                           then fun e =>
                                  Sorted _ _ (typ_pi _ e typA typB)
                                    (typ_star _ (strong_to_weak_ctx_wf _ _ H))
                           else fun _ => Untyped _ _ _) eq_refl
                    | _ => fun _ => Untyped _ _ _
                    end (
                        let H' : T ≻* whnormalize_typed T H' := whnormalize_typed_step_star _ _
                        in typ_conv _ typB (Requiv_clot_star H')
                             (subject_reduction _ _ _ _ _ typT H')
                      )
                | _ => Untyped _ _ _
                end
          | _ => fun _ => Untyped _ _ _
          end (
              let H' : T ≻* whnormalize_typed T H' := whnormalize_typed_step_star _ _ in
              typ_conv _ typA (Requiv_clot_star H') (subject_reduction _ _ _ _ _ typT H')
            )
      | _ => Untyped _ _ _
      end
  | Abs A t =>
      match infer_aux Sc H A with
      | Kind typA =>
          match infer_aux Sc (strong_cons_wf _ _ H typA) t with
          | Kind typt => Untyped _ _ _
          | Sorted B s' typt typB => 
              (if Sc Box s' as b return Sc Box s' = b -> _
               then fun e =>
                      Sorted _ _
                        (typ_abs _ e typA typB typt)
                        (typ_pi _ e typA typB)
               else fun _ => Untyped _ _ _) eq_refl
          | _ => Untyped _ _ _
          end
      | Sorted T s typA typT =>
          let H' := ex_intro _ _ (ex_intro _ _ (ex_intro _ _ typT)) in
          match whnormalize_typed T H' as T' return Γ ⊢(Sc) A : T' -> _
          with
          | Srt Star =>
              fun typA =>
                match infer_aux Sc (strong_cons_wf _ _ H typA) t with
                | Kind typt => Untyped _ _ _
                | Sorted B s' typt typB => 
                    (if Sc Star s' as b return Sc Star s' = b -> _
                     then fun e =>
                            Sorted _ _
                              (typ_abs _ e typA typB typt)
                              (typ_pi _ e typA typB)
                     else fun _ => Untyped _ _ _) eq_refl
                | _ => Untyped _ _ _
                end
          | _ => fun _ => Untyped _ _ _
          end (
              let H' : T ≻* whnormalize_typed T H' := whnormalize_typed_step_star _ _ in
              typ_conv _ typA (Requiv_clot_star H') (subject_reduction _ _ _ _ _ typT H')
            )
      | _ => Untyped _ _ _
      end
  | App t u =>
      match infer_aux Sc H t with
      | Sorted T s' typt typT =>
          let H' := ex_intro _ _ (ex_intro _ _ (ex_intro _ _ typT)) in
          match whnormalize_typed T H' as T' return Γ ⊢(Sc) t : T' -> Γ ⊢(Sc) T' : Srt s' -> _
          with
          | Pi A B =>
              fun typt typPi =>
                (fun  H' : exists s, Γ ⊢(Sc) A : Srt s /\ Γ ; A ⊢(Sc) B: Srt s' =>
                   match infer_aux Sc H u with
                   | Sorted U s typu typU =>
                       match convertible_typed (ex_intro _ _ typU)
                               (let (s, H') := H' in
                                let (typA, _) := H' in
                                ex_intro _ _ typA)
                       with
                       | left Hconv =>
                           Sorted _ _
                             (typ_app _ typt
                                (let (_, H') := H' in
                                 let (typA, _) := H' in
                                 typ_conv _ typu Hconv typA
                             ))
                             (let (_, H') := H' in
                              let (typA, typB) := H' in
                              bind_first_typ (typ_conv _ typu Hconv typA) typB :
                                (Γ ⊢(Sc) _ : bind (bind_first u) (Srt s'))
                             )
                       | right _ => Untyped _ _ _
                       end
                   (* -2 Goal *)
                   | Kind typu =>
                       Untyped _ _ _
                   | _ => Untyped _ _ _
                   end
                )
                  (
                    let (s, H') := typ_pi_inv _ _ _ _ _ typPi in
                    let (s__c, H') := H' in
                    let (srt_eq, H') := H' in
                    let (typA, H') := H' in
                    let (typB, _) := H' in
                    ex_intro _ s (
                        conj typA
                          (
                            let e := srt_equiv_srt srt_eq in
                            match eq_sym e with
                            | eq_refl => typB
                            end
                          )
                      )
                  )
          | _ => fun _ _ => Untyped _ _ _
          end
            (typ_conv _ typt (Requiv_clot_star (whnormalize_typed_step_star _ _))
               (whnormalize_typed_preserves _ _ _ _ _ typT)
            )
            (whnormalize_typed_preserves _ _ _ _ _ typT)
      | _ => Untyped _ _ _
      end
  end.

Lemma typed_infer_aux_not_untyped Sc {n} Γ (H: strong_ctx_wf Sc Γ) (t T: term n) :
  Γ ⊢(Sc) t : T -> match infer_aux Sc H t with Untyped _ _ _ => False | _ => True end.
Proof.
  induction 1; simpl; auto.
  - specialize (IHtyping1 H). destruct (infer_aux _ _ A) as [| typA |]; try tauto.
    + assert (s = Box).
      { eapply srt_equiv_srt. eapply unique_typing; eassumption. } subst.
      clear H0_. rename H0 into pi_check.
      specialize (IHtyping2 (strong_cons_wf _ _ H typA)).
      destruct (infer_aux _ _ _); try tauto.
      * generalize (@eq_refl _ (Sc Box Box)). generalize (Sc Box Box) at 2 3.
        destruct b; try tauto. intro. unfold pi_scheme_check in *.
        assert (s' = Box).
        { eapply srt_equiv_srt. eapply unique_typing; eassumption. }
        subst. congruence.
      * assert (T ≻* Srt s').
        { eapply srt_equiv. eapply unique_typing; try eassumption. }
        match goal with |- context[match _ with _ => _ end ?x] => generalize x end.
        set (whnormalize_typed _ _).
        assert (t ≻* Srt s').
        { eapply confluence_step in H0 as [v [norm_red srt_red]]; swap 1 2.
          { apply whnormalize_typed_step_star. } apply srt_star in srt_red. subst.
          exact norm_red. }
        assert (t ≅ Srt s').
        { apply Requiv_clot_star. assumption. }
        assert (t = Srt s').
        { pose proof (whnft := whnormalize_typed_whnf _ _ : whnf t).
          epose proof (whnf_is_sort_type_or_never_will_be whnft).
          destruct t; try firstorder. f_equal. eapply srt_equiv_srt. eassumption. }
        rewrite H3.
        assert (typs' : Γ; A ⊢(Sc) Srt s' : Srt s).
        { eapply subject_reduction; try eassumption. }
        assert (s' = Star).
        { destruct s'; auto. exfalso. revert typs'. clear. generalize (@Srt (S n) s) as T. intro.
          remember (Srt Box). induction 1 in Heqt |- *; try discriminate; tauto. }
        subst. intro. generalize (@eq_refl _ (Sc Box Star)).
        generalize (Sc Box Star) at 2 3. destruct b; auto. congruence.
    + assert (T ≻* Srt s).
        { eapply srt_equiv. eapply unique_typing; try eassumption. }
        match goal with |- context[match _ with _ => _ end ?x] => generalize x end.
        set (whnormalize_typed _ _).
        assert (t ≻* Srt s).
        { eapply confluence_step in H1 as [v [norm_red srt_red]]; swap 1 2.
          { apply whnormalize_typed_step_star. } apply srt_star in srt_red. subst.
          exact norm_red. }
        assert (t ≅ Srt s).
        { apply Requiv_clot_star. assumption. }
        assert (t = Srt s).
        { pose proof (whnft := whnormalize_typed_whnf _ _ : whnf t).
          epose proof (whnf_is_sort_type_or_never_will_be whnft).
          destruct t; try firstorder. f_equal. eapply srt_equiv_srt. eassumption. }
        rewrite H4. clear dependent t.
        assert (typs : Γ ⊢(Sc) Srt s : Srt s0) by (eauto using subject_reduction).
        assert (s = Star).
        { destruct s; auto. exfalso. revert typs. clear. generalize (@Srt (S n) s0) as T. intro.
          remember (Srt Box). clear T. induction 1 in Heqt |- *; try discriminate; tauto. }
        subst. intro typA. clear dependent T.
        specialize (IHtyping2 (strong_cons_wf _ _ H typA)). destruct (infer_aux _ _ _); try tauto.
      * generalize (@eq_refl _ (Sc Star Box)). generalize (Sc Star Box) at 2 3.
        destruct b; try tauto. intro. unfold pi_scheme_check in *.
        assert (s' = Box).
        { eapply srt_equiv_srt. eapply unique_typing; eassumption. }
        subst. congruence.
      * assert (T ≻* Srt s').
        { eapply srt_equiv. eapply unique_typing; try eassumption. }
        match goal with |- context[match _ with _ => _ end ?x] => generalize x end.
        set (whnormalize_typed _ _).
        assert (t ≻* Srt s').
        { eapply confluence_step in H1 as [v [norm_red srt_red]]; swap 1 2.
          { apply whnormalize_typed_step_star. } apply srt_star in srt_red. subst.
          exact norm_red. }
        assert (t ≅ Srt s').
        { apply Requiv_clot_star. assumption. }
        assert (t = Srt s').
        { pose proof (whnft := whnormalize_typed_whnf _ _ : whnf t).
          epose proof (whnf_is_sort_type_or_never_will_be whnft).
          destruct t; try firstorder. f_equal. eapply srt_equiv_srt. eassumption. }
        rewrite H4.
        assert (typs' : Γ; A ⊢(Sc) Srt s' : Srt s).
        { eapply subject_reduction; try eassumption. }
        assert (s' = Star).
        { destruct s'; auto. exfalso. revert typs'. clear. generalize (@Srt (S n) s) as T. intro.
          remember (Srt Box). induction 1 in Heqt |- *; try discriminate; tauto. }
        subst. intro. generalize (@eq_refl _ (Sc Star Star)).
        generalize (Sc Star Star) at 2 3. destruct b; auto. congruence.
  - specialize (IHtyping1 H). destruct (infer_aux _ _ A); try tauto.
    + specialize (IHtyping3 (strong_cons_wf _ Box H typt)).
      destruct (infer_aux _ _ _); try tauto.
      * cut (Γ; A ⊢(Sc) Srt Box : Srt s').
        { clear. remember (Srt Box). induction 1 in Heqt |- *; try discriminate; tauto. }
        eapply subject_reduction; try eassumption. eapply srt_equiv.
        eapply unique_typing; try eassumption.
      * generalize (@eq_refl _ (Sc Box s0)). generalize (Sc Box s0) at 2 3.
        destruct b; auto.
        assert (s = Box). {eapply srt_equiv_srt. eapply unique_typing; eassumption. }
        subst. enough (s' = s0) by congruence.
        assert (T ≅ B) by eauto using unique_typing.
        apply (@srt_equiv_srt (S n)). revert H0_0 typT H1.
        generalize (Γ; A) (@Srt (S n) s') (@Srt (S n) s0). clear.
        rename B into t, T into u. intros Γ X Y typB typT Hcong.
        eapply equiv_both_star in Hcong as [v [redu redt]].
        eapply unique_typing; eapply subject_reduction; eauto.
    + assert (T ≻* Srt s).
      { eapply srt_equiv. eapply unique_typing; try eassumption. }
      match goal with |- context[match _ with _ => _ end ?x] => generalize x end.
      set (whnormalize_typed _ _) as u.
      assert (u ≻* Srt s).
      { eapply confluence_step in H1 as [v [norm_red srt_red]]; swap 1 2.
        { apply whnormalize_typed_step_star. } apply srt_star in srt_red. subst.
        exact norm_red. }
      assert (u ≅ Srt s).
      { apply Requiv_clot_star. assumption. }
      assert (u = Srt s).
      { pose proof (whnfu := whnormalize_typed_whnf _ _ : whnf u).
        epose proof (whnf_is_sort_type_or_never_will_be whnfu).
        destruct u; try firstorder. f_equal. eapply srt_equiv_srt. eassumption. }
      rewrite H4. clear dependent u.
      assert (typs : Γ ⊢(Sc) Srt s : Srt s0) by (eauto using subject_reduction).
      assert (s = Star).
      { destruct s; auto. exfalso. revert typs. clear. generalize (@Srt (S n) s0) as T. intro.
        remember (Srt Box). clear T. induction 1 in Heqt |- *; try discriminate; tauto. }
      subst. intro typA. clear dependent T.
      specialize (IHtyping3 (strong_cons_wf _ _ H typA)). destruct (infer_aux _ _ _); try tauto.
      * cut (Γ; A ⊢(Sc) Srt Box : Srt s').
        { clear. remember (Srt Box). induction 1 in Heqt |- *; try discriminate; tauto. }
        eapply subject_reduction; try eassumption. eapply srt_equiv.
        eapply unique_typing; try eassumption.
      * generalize (@eq_refl _ (Sc Star s)). generalize (Sc Star s) at 2 3.
        destruct b; auto.
        enough (s = s') by congruence.
        assert (T ≅ B) by eauto using unique_typing.
        apply (@srt_equiv_srt (S n)). revert H0_0 typT H1.
        generalize (Γ; A) (@Srt (S n) s') (@Srt (S n) s0). clear.
        rename B into t, T into u. intros Γ X Y typB typT Hcong.
        eapply equiv_both_star in Hcong as [v [redu redt]].
        eapply unique_typing; eapply subject_reduction; eauto.
  - specialize (IHtyping1 H). destruct (infer_aux _ _ t); try tauto.
    { assert (e: Srt Box ≅ Pi A B) by eauto using unique_typing.
      eapply srt_equiv, pi_star in e. firstorder discriminate. }
      match goal with |- context[match _ with _ => _ end ?x ?y] => generalize x y end.
    set (whnormalize_typed _ _) as T'.
    pose proof (whnft := whnormalize_typed_whnf _ _ : whnf T').
    epose proof (whnf_is_pi_type_or_never_will_be whnft). intros typt' typT'.
    assert (T' ≅ Pi A B) by eauto using unique_typing.
    match goal with |- context[match _ with _ => _ end ?x typT'] => generalize x end.
    destruct T'; try solve [firstorder]. intro typt''.
    specialize (IHtyping2 H). destruct (infer_aux _ _ _); try tauto.
    { assert (Hcong : A ≅ Srt Box) by eauto using unique_typing. revert H0_ Hcong. clear.
      intros Htyp Hcong. apply srt_typing in Htyp as [|[s Htyp]]; try discriminate.
      apply typ_pi_inv in Htyp as [s' [_ [_ [typA _]]]]. apply Requiv_sym, srt_equiv in Hcong.
      assert (c : Γ ⊢(Sc) Srt Box: Srt s') by eauto using subject_reduction.
      revert c. clear. remember (Srt Box). induction 1; try discriminate; tauto. }
    destruct (convertible_typed _ _); auto.
    apply n0. assert (Hcong : T0 ≅ A) by eauto using unique_typing.
    apply (Requiv_trans Hcong). revert H1. clear. intro H. apply pi_equiv_pi in H.
    intuition auto using Requiv_sym.
  - apply IHtyping1.
Qed.

Definition infer Sc {n} {Γ} (H: strong_ctx_wf Sc Γ) (t: term n) : option (term n) :=
  match infer_aux Sc H t with
  | Untyped _ _ _ => None
  | Kind _ => Some (Srt Box)
  | Sorted T _ _ _ => Some T
  end.

Lemma infer_some Sc {n} {Γ} (H: strong_ctx_wf Sc Γ) (t: term n) T :
  infer Sc H t = Some T -> Γ ⊢(Sc) t : T.
Proof.
  unfold infer.
  destruct (infer_aux _ _ _); try discriminate; inversion 1; subst; auto.
Qed.

Lemma infer_none Sc {n} {Γ} (H: strong_ctx_wf Sc Γ) (t: term n) :
  infer Sc H t = None -> forall T, ¬ (Γ ⊢(Sc) t : T).
Proof.
  unfold infer.
  destruct (infer_aux _ _) eqn: e; try discriminate. intros _ T typt.
  eapply typed_infer_aux_not_untyped in typt. rewrite e in typt. assumption.
Qed.

Definition infer_dec Sc {n} {Γ} (H: strong_ctx_wf Sc Γ) (t: term n) :
  { T | Γ ⊢(Sc) t : T } + {forall T, ¬ (Γ ⊢(Sc) t : T)} :=
  match infer Sc H t as o return infer Sc H t = o -> _ with
     | None => fun e => inright (infer_none _ _ _ e)
     | Some T => fun e => inleft (exist _ T (infer_some _ _ _ _ e))
  end eq_refl.

Definition infer_dec_closed Sc (t: term 0) :
  { T | \ ⊢(Sc) t : T } + {forall T, ¬ (\ ⊢(Sc) t : T)} :=
  infer_dec Sc (strong_empty_wf Sc) t.
