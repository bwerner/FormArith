From FormArith.SimplyTypedLambdaCalculus Require Import Definitions.
Import List.ListNotations.


Inductive SN: term -> Prop :=
  | Strong (t: term) :
      (forall (t': term), t ~> t' -> SN t') -> SN t.

Fixpoint reducible (A: type) (t: term): Prop :=
  match A with
  | Base => SN t
  | Arr A B => forall (u: term), reducible A u -> reducible B (App t u)
  end.

Definition neutral (t: term): Prop :=
  match t with
  | Lam _ => False
  | _ => True
  end.

Inductive sub_term: term -> term -> Prop :=
  | Sub_app1 (t1 t2: term) : sub_term t1 (App t1 t2)
  | Sub_app2 (t1 t2: term) : sub_term t2 (App t1 t2)
  | Sub_lam (t: term) : sub_term t (Lam t).


Lemma SN_lam (t: term):
  SN t -> SN (Lam t).
Proof.
  revert t.

  apply SN_ind; intros ? _ H.
  apply Strong; intros ? Hbeta.
  inversion Hbeta; subst.
  now apply H.
Qed.

Lemma SN_sub_term (t: term):
  SN t -> forall (t': term), sub_term t' t -> SN t'.
Proof.
  induction 1 as [ ? _ IH ].
  inversion 1; subst.
  all: apply Strong; intros u ?.

  all: match goal with
       | H: sub_term _ (App ?t ?t') |- _ => rename t into t1; rename t' into t2
       | H: _ |- _ => idtac
       end.

  - apply IH with (App u t2).
    + now apply Beta_AppL.
    + apply Sub_app1.

  - apply IH with (App t1 u).
    + now apply Beta_AppR.
    + apply Sub_app2.

  - apply IH with (Lam u).
    + now apply Beta_Lam.
    + apply Sub_lam.
Qed.

Lemma SN_var_app (t: term) (n: var):
  SN (App t (Var n)) -> SN t.
Proof.
  intros ?.
  apply (SN_sub_term (App t (Var n))); [ assumption |].
  apply Sub_app1.
Qed.

Lemma SN_inverted (t: term):
  SN t -> forall (t': term), t ~> t' -> SN t'.
Proof.
  now inversion 1.
Qed.

Fixpoint atomic' (t: term):=
  match t with 
  | Var _ => True (* unsure if this case should be included or not? *)
  | App l _ => atomic' l
| _ => False
  end.

Definition atomic (t: term) := atomic' t /\ SN t.

Lemma SN_subst (t: term) (σ: var -> term):
  SN t -> forall (u: term), t = u.[σ] -> SN u.
Proof.
  induction 1 as [? _ IHt]; intros; subst.

  apply Strong.
  intros t ?.

  apply IHt with t.[σ].
  - now apply beta_subst.
  - reflexivity.
Qed.

(*Lemma 3.2.1 (3) refers to terms of this specific shape*)
Fixpoint nested_app t l :=
  match l with 
  | nil => t
  | cons t' l' => App (nested_app t l') t'
  end.

Lemma atomic_step t s : atomic' t -> t ->β s -> atomic' s.
Proof.
  induction t in s |- *; cbn.
  - inversion 2.
  - intros Hat Hstep. inversion Hstep; subst.
    + contradiction.
    + cbn. apply IHt1; assumption.
    + cbn. assumption.
  - tauto.
Qed.

Lemma atomic_app_r t u : atomic t -> SN u -> atomic (App t u).
Proof.
  intros [Hat Hsnt] Hsnu.
  split.
  - tauto.
  - induction Hsnt in Hat, u, Hsnu |-*.
    induction Hsnu in H0 |- *.
    constructor. intros t' Hstep.
    inversion Hstep; subst.
    + contradiction.
    + apply H0.
      * assumption.
      * eapply atomic_step; eassumption.
      * constructor. assumption.
    + apply H2. 1: assumption. assumption.
Qed.

Lemma SN_ind_pair (P : term -> term -> Prop):
  (forall t u, (forall t' u', ((t = t' /\ u ->β u') \/ (t ->β t' /\ u = u')) -> P t' u') -> P t u)
    -> forall t u, SN t -> SN u -> P t u.
Proof.
  intros IH ? ? Hsnt.
  revert u.

  induction Hsnt as [? _ IHt].
  intros ? Hsnt.

  induction Hsnt as [? ? IHv].
  apply IH.

  intros ? ? [[? ?] | [? ?]]; subst.
  - now apply IHv.
  - apply IHt; [ assumption |].
    now apply Strong.
Qed.

(*
  Enumerate all the possible next steps of a term.
  This is helpful (and probably only helpful) for the max_steps lemma.
*)
Fixpoint enumerate_steps (t : term) : list term :=
  match t with 
  | Var _ => []
  | Lam s => List.map Lam (enumerate_steps s)
  | App s t => List.map (fun s => App s t) (enumerate_steps s)
                ++ List.map (fun t => App s t) (enumerate_steps t)
                ++ match s with
                   | Lam s' => [s'.[t/]]
                   | __ => []
                   end
  end.

(*
  enumerate_steps is sound and complete:
 *)
Lemma enumerate_steps_spec t: forall t', List.In t' (enumerate_steps t) <-> t ->β t'.
Proof.
  induction t as [x | s IHs t IHt | s IHs].
  - intros u; cbn. split.
    + firstorder.
    + inversion 1.
  - intros u; cbn. split.
    + intros Hin. apply List.in_app_or in Hin as [Hin | Hin]. 2: apply List.in_app_or in Hin as [Hin | Hin].
      * rewrite List.in_map_iff in Hin. destruct Hin as  [s' [<- Hs']].
        apply IHs in Hs'.
        now constructor.
      * rewrite List.in_map_iff in Hin. destruct Hin as [t' [<- Ht']].
        apply IHt in Ht'.
        now constructor.
      * destruct s; try firstorder.
        now constructor.
    + intros Hstep. inversion Hstep; subst.
      * apply List.in_or_app. right. apply List.in_or_app. right.
        firstorder.
      * apply List.in_or_app. left.
        apply (List.in_map (fun s' => App s' t)).
        now apply IHs.
      * apply List.in_or_app. right. apply List.in_or_app. left.
        apply (List.in_map (fun t' => App s t')).
        now apply IHt.
  - intros u; cbn. split.
    + intros Hin. apply List.in_map_iff in Hin.
      destruct Hin as [s' [<- Hs']].
      apply IHs in Hs'.
      now constructor.
    + inversion 1; subst.
      apply List.in_map. now apply IHs.
Qed.

(*
  This version is slightly nicer to use in the following proof:
*)
Lemma enumerate_Forall_beta t : List.Forall (fun t' => t ->β t') (enumerate_steps t).
Proof.
  apply List.Forall_forall.
  apply enumerate_steps_spec.
Qed.

(*
  reduction_sequences are lists where any element beta-reduces to the next element.
  This helps us reason about the number of reduction steps any term can take.
 *)
Fixpoint reduction_sequence (l : list term) : Prop :=
  match l with 
  | nil => True
  | cons t nil => True
  | cons s (cons t l' as ll) => s ->β t /\ reduction_sequence ll
  end.

Require Import Lia.

(*
  Any strongly normalizing term has a maximum number of steps it can reduce.
  We state this by stating a maximal length for any reduction sequence.

  Intuitively, this is by induction on SN, which gives us the induction hypothesis for each possible next step.
   The correctness proof follows since for any reduction sequence starting in t and with first step t', the remaining sequence must be a reduction sequence for t', so the induction hypothesis applies.
  In practice, it is much more difficult, since we need to determine the maximum of the (existentially quantified) numbers of steps for each next term.
*)
Lemma max_steps (t: term) : SN t -> exists n, forall l, reduction_sequence (t :: l) -> length l <= n.
Proof.
  (*The proof is by induction on SN, which is also why we can't (easily) state this as a function.*)
  intros Hsn. induction Hsn as [t Hsn IH].
  (*First, we apply the induction hypothesis to all terms in `enumerate_steps` (i.e. all the terms t can reduce to).*)
  assert (List.Forall (fun t' => t ->β t' /\ exists n, forall l, reduction_sequence (t' :: l) -> length l <= n) (enumerate_steps t)) as H.
  + pose proof (enumerate_Forall_beta t) as H.
    induction H.
    * constructor.
    * constructor. 2: assumption.
      firstorder.
  + (*Unfortunately, the maximal lengths for all t' are currently hidden underneath existential quantifiers, and not easily accessible.
      We begin by moving them into an existentially quantified list.*)
    assert (exists l', length l' = length (enumerate_steps t) /\ List.Forall (fun (p : term * nat) => let (t', n) := p in forall l, reduction_sequence (t' :: l) -> length l <= n) (List.combine (enumerate_steps t) l')) as [l' [Hlen Hl']].
    * induction H as [|t' l Ht' HForall IHForall].
      -- exists nil. firstorder.
      -- destruct Ht' as [_ [n Hn]].
         destruct IHForall as [l' Hl'].
         exists (cons n l').
         split.
         ++ cbn. firstorder.
         ++ constructor; firstorder.
    * (* We now have l', the list of the maximal number of steps for each term in `enumerate_steps t`.*)
      (* Clearly, we need at least one more step:*)
      exists (S(List.list_max l')).
      clear - l' Hlen Hl'.
      (* For the correctness proof, we inspect the reduction sequence:*)
      intros l Hred.
      destruct l as [|t' l]. 1: cbn; lia. (*empty reduction sequences are trivial.*)
      (* The first step in the reduction sequence must be a valid reduction step, so we must also have the next term in enumerate_steps.
         Intuitively, we should thus be able to apply Hl'; but this requires some more difficulty:
      *)
      destruct Hred as [Hbeta Hred].
      rewrite <- enumerate_steps_spec in Hbeta.
      (* We first need to obtain the index of t', so that we can recover its associated number of steps.*)
      apply List.In_nth with (d := Var 0) in Hbeta. destruct Hbeta  as (ind & Hind & Hbeta).
      pose (List.nth ind l' 0) as n'.
      (* n' is the max number of steps of t', but we need to recover this fact.
         It is stored in Hl', so we need to instantiate the `Forall` with the corresponding index:
      *)
      pose (List.nth ind (List.combine (enumerate_steps t) l') (Var 0, 0)) as p.
      assert (p = (t', n')) as Heq by (subst; now apply List.combine_nth).
      assert (List.In p (List.combine (enumerate_steps t) l')) as Hp.
      { apply List.nth_In.
        pose proof (List.combine_length (enumerate_steps t) l').
        lia.
      }
      rewrite List.Forall_forall in Hl'. apply Hl' in Hp.
      rewrite Heq in Hp.
      (* After all this, we have recovered what is essentially the induction hypothesis for t'.
        Since (t :: t' :: l) is a valid reduction sequence for t, (t' :: l) must be a valid reduction sequence for t'; thus, the IH applies.
       *)
      specialize (Hp l).
      assert (n' <= List.list_max l'). (*This is more or less the definition of list_max, but apparently, it is not in the library directly?*)
      { assert (List.list_max l' <= List.list_max l') as H by constructor.
        rewrite List.list_max_le in H.
        rewrite List.Forall_forall in H.
        apply H.
        apply List.nth_In. congruence.
      }
      apply Hp in Hred.
      cbn. lia.
Qed.

(* The standard strong induction on natural numbers *)
Lemma nat_strong_ind:
  forall P: nat -> Prop, (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n.
Proof.
  intros P Hind n.
  enough (forall m, m <= n -> P m) as H.
  - apply H. constructor.
  - induction n.
    + intros m. destruct m.
      * intros _. apply Hind.
        lia.
      * lia.
    + intros m Hm.
      inversion Hm.
      * subst. apply Hind.
        intros m' Hm'.
        apply IHn. lia.
      * subst. now apply IHn.
Qed.

(* Lemma 3.2.1 statement (3) for the base case, where the entire term is of some atomic type.
   Formalizing this proof is difficult:
   While intuitively, any reduction step is either within any subterm (not changing the specified shape) or reduction of the leftmost application,
   the main difficulty in Coq stems from the fact that we do not know the size of the term (i.e. the number of applications).

   The current attempt uses the maximal numbers of steps (as determined by max_steps),
   but is stuck at destructing the actual reduction step. Presumably, induction is needed, but I have not yet found a version that yields suitable induction hypotheses.
*)
Lemma base_case t u l : SN (nested_app t.[u/] l) -> SN u -> forall t', nested_app (App (Lam t) u) l ->β t' -> SN t'.
Proof.
  intros Hsn Hsnu.
  (*determine the maximum number of steps for t*)
  assert (exists nt, forall l, reduction_sequence (t :: l) -> length l <= nt) as [nt Hnt].
  { admit. } (*chore: we don't have a lemma to do this yet, so induction on l?*)
  (*determine the maximum number of steps for u*)
  assert (exists nu, forall l, reduction_sequence (u :: l) -> length l <= nu) as [nu Hnu].
  { apply max_steps. assumption. }
  (*determine the maximum number of steps for all terms in l*)
  assert (exists l', length l' = length l /\ List.Forall (fun (p : term * nat) => let (t, n) := p in forall l, reduction_sequence (t :: l) -> length l <= n) (List.combine l l')) as [l' Hl'].
  { induction l.
    - exists nil; firstorder.
    - cbn in Hsn.
      assert (SN a) as Ha.
      { eapply SN_sub_term. 1: exact Hsn. constructor. }
      assert (SN (nested_app t.[u/] l)) as Hsn'.
      { eapply SN_sub_term. 1: exact Hsn. constructor. }
      specialize (IHl Hsn').
      destruct IHl as [l' Hl'].
      apply max_steps in Ha.
      destruct Ha as [n Hn].
      exists (cons n l').
      cbn. firstorder.
  }
  (*We wish to do induction on the sum of all these step numbers: This will allow us to use the induction hypothesis for any step in any of these terms.*)
  remember (nt + nu + List.list_sum l') as n.
  (*We do induction on n with everything else quantified.*)
  induction n as [n IH] using nat_strong_ind in t, u, l, Hsn, Hsnu, nt, Hnt, nu, Hnu, l', Hl', Heqn |- *.
  intros t' Hstep.

  change l with (app nil l) in *.
  change (SN (nested_app t' nil)).
  cbn in Hstep.
  remember nil as outer.
  
  remember (nested_app (App (Lam t) u) l) as trm.
  induction Hstep in t, u, l, outer, Hsn, Hsnu, nt, Hnt, nu, Hnu, l', Hl', Heqn, Heqtrm |- *.
  - subst.
    destruct l.
    + cbn in Heqtrm. inversion Heqtrm; subst. rewrite List.app_nil_r in Hsn. assumption.
+ cbn in Heqtrm. inversion Heqtrm; subst.
      destruct l; cbn in *; congruence.
  - subst.
    destruct l; cbn in *.
    + inversion Heqtrm; subst.
      inversion Hstep; subst.
      constructor. eapply IH; admit.
    + assert (nested_app (App s' t0) outer = nested_app s' (outer ++ [t0])) as -> by admit.
      inversion Heqtrm; subst.
      eapply IHHstep.
      2: exact Hsnu.
      2: exact Hnt.
      2: exact Hnu.
      3, 4: reflexivity.
      1, 2: assert ((outer ++ [t1]) ++ l = outer ++ (t1 :: l))%list as -> by admit.
      all: assumption.
  - destruct l; cbn in *.
    + inversion Heqtrm; subst.
      constructor. eapply IH; admit.
    + inversion Heqtrm; subst.
      change (SN (nested_app (nested_app (App (Lam t) u) (t' :: l)) outer)).
      assert ((nested_app (nested_app (App (Lam t) u) (t' :: l)) outer) = nested_app (App (Lam t) u) (outer ++ (t' :: l))) as -> by admit.
      eapply IH.
      2: exact Hsn.
      2: exact Hsnu.
      2, 3: eassumption.
      3: reflexivity.
      all: admit.
  - destruct l; cbn in Heqtrm; congruence.
Admitted.

(*Lemma 3.2.1 of the lecture notes.*)
Lemma reducible_is_SN_variant_1 (A : type):
  (forall (t: term), reducible A t -> SN t) /\
  (forall (t: term), atomic t -> reducible A t) /\
  (forall (t u: term) l, reducible A (nested_app (t.[u .: ids]) l) -> SN u -> reducible A (nested_app (App (Lam t) u) l)).
Proof.
  induction A as [ | A1 IHA1 A2 IHA2 ].
  - split. 2: split.
    (*the first two statements are easy in the base case.*)
    + intros t Ht. constructor. intros t'.
      apply SN_inverted. assumption.
    + intros t [_ Hsnt]. now destruct Hsnt.
    + intros t u l H Hsnu. cbn in *. 
      constructor.
      (*the third statement is very difficult: see above.*)
      now apply base_case.
  - split. 2: split.
    + cbn. intros t Hred.
      apply SN_sub_term with (t := App t (Var 0)).
      2: constructor.
      apply IHA2, Hred.
      apply IHA1. split. 
      * cbn. tauto.
      * constructor. intros ? H. inversion H.
    + cbn. intros t Hat u Hred.
      apply IHA2. split.
      * apply Hat.
      * apply IHA1 in Hred.
        apply atomic_app_r; assumption.
    + intros t u l Hred Hsnu u' Hred'.
      change (reducible A2 (nested_app (App (Lam t) u) (cons u' l))).
      apply IHA2.
      * cbn. now apply Hred.
      * assumption.
Qed.

Lemma reducible_is_SN (A : type):
  (forall (t: term), reducible A t -> SN t) /\
    (forall (t u: term), reducible A t -> t ~> u -> reducible A u) /\
    (forall (t: term), neutral t -> (forall (t': term), t ~> t' -> reducible A t') -> reducible A t).
Proof.
  induction A as [ | A [IHA1 [IHA2 IHA3]] B [IHB1 [IHB2 IHB3]] ].
  - do 3 split.
    + intros.
      apply SN_inverted with t'; [| assumption ].
      now apply SN_inverted with t.

    + intros.
      apply SN_inverted with u; [| assumption ].
      now apply SN_inverted with t.

    + assumption.

  - split; [| split ]; simpl.
    + intros ? Hred.
      apply Strong.

      intros ? ?.
      apply SN_inverted with t; [| assumption ].
      apply SN_var_app with 0.

      apply IHB1.
      apply Hred.
      apply IHA3; [ exact I |].
      inversion 1.

    + intros t ? IHred ? u Hred.
      apply IHB2 with (App t u).
      * apply IHred, Hred.
      * now apply Beta_AppL.

    + intros ? ? Hredt ? Hredu.
      apply IHA1 in Hredu as HSNu.
      induction HSNu as [ u _ IHu ].

      apply IHB3; [ exact I |].
      inversion 1; subst.
      * contradiction.
      * now apply Hredt.
      * apply IHu; [ assumption |].
        now apply IHA2 with u.
Qed.

Lemma SN_ind_pair (P : term -> term -> Prop):
  (forall t u, (forall t' u', ((t = t' /\ u ~> u') \/ (t ~> t' /\ u = u')) -> P t' u') -> P t u)
    -> forall t u, SN t -> SN u -> P t u.
Proof.
  intros IH ? ? Hsnt.
  revert u.

  induction Hsnt as [? _ IHt].
  intros ? Hsnt.

  induction Hsnt as [? ? IHv].
  apply IH.

  intros ? ? [[? ?] | [? ?]]; subst.
  - now apply IHv.
  - apply IHt; [ assumption |].
    now apply Strong.
Qed.

Lemma reducible_abs (v: term) (A B: type):
  (forall (u: term), reducible A u -> reducible B v.[u/]) -> reducible (Arr A B) (Lam v).
Proof.
  intros Hred u Hredu.
  specialize (reducible_is_SN A) as [HA1 [HA2 HA3]].
  specialize (reducible_is_SN B) as [HB1 [HB2 HB3]].

  assert (HSNu: SN u) by now apply HA1.
  assert (HSNv: SN v).
  { apply SN_subst with v.[u/] (u .: ids); [| reflexivity ].
    apply HB1.
    now apply Hred. }

  revert Hred Hredu.
  apply SN_ind_pair with (t := v) (u := u).
  2: { apply HSNv. }
  2: { apply HSNu. }

  intros x y IH Hred Hredy.
  apply HB3; [ exact I |].
  intros t Hbeta.

  inversion Hbeta; subst.
  - now apply Hred.

  - inversion H2; subst.
    apply IH; [ .. | assumption ].
    { now right. }

    intros.
    apply HB2 with x.[u0/].
    + now apply Hred.
    + now apply beta_subst.

  - apply IH.
    + now left.
    + now apply Hred.
    + now apply HA2 with y.
Qed.


Lemma reducible_var (A: type) (x: var) (Γ: var -> type):
  Γ ⊢ Var x : A -> reducible A (Var x).
Proof.
  intros.
  destruct A.
  - simpl.
    apply Strong.
    inversion 1.
  - apply reducible_is_SN; [ exact I |].
    inversion 1.
Qed.

Lemma typing_is_reducible (Γ: var -> type) (σ: var -> term):
  (forall (x: var), reducible (Γ x) (σ x)) ->
    forall (A: type) (t: term), Γ ⊢ t : A -> reducible A t.[σ].
Proof.
  intros Hred A t.
  revert Hred.
  revert σ A Γ.

  induction t; intros σ A Γ Hred.
  all: inversion 1; subst; simpl.

  - apply Hred.
  - apply IHt1 with (σ := σ) in H2; [| assumption ].
    apply IHt2 with (σ := σ) in H4; [| assumption ].
    now apply H2.
  - apply reducible_abs.
    intros u Hredu. asimpl.
    apply IHt with (A0 .: Γ); [| assumption ].
    intros [| x ]; simpl; [ assumption |].
    apply Hred.
Qed.

Corollary STLC_is_SN (A: type) (Γ: var -> type) (t: term):
  Γ ⊢ t : A -> SN t.
Proof.
  intros.
  apply (reducible_is_SN A).
  replace t with t.[ids] by apply subst_id.
  apply typing_is_reducible with Γ; [| assumption ].
  intros.
  apply reducible_var with Γ.
  now apply Typing_Var.
Qed.
