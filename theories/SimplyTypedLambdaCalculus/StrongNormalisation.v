From FormArith.SimplyTypedLambdaCalculus Require Import Definitions ChurchRosser.
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

Lemma atomic_step t s : atomic' t -> t ~> s -> atomic' s.
Proof.
  induction t as [|t1 IH1 t2 IH2|] in s |- *; cbn.
  - inversion 2.
  - intros Hat Hstep. inversion Hstep; subst.
    + contradiction.
    + cbn. apply IH1; assumption.
    + cbn. assumption.
  - tauto.
Qed.

Lemma atomic_app_r t u : atomic t -> SN u -> atomic (App t u).
Proof.
  intros [Hat Hsnt] Hsnu.
  split.
  - tauto.
  - induction Hsnt as [t Hsnt IHsnt] in Hat, u, Hsnu |-*.
    induction Hsnu as [u Hsnu IHsnu].
    constructor. intros t' Hstep.
    inversion Hstep; subst.
    + contradiction.
    + apply IHsnt.
      * assumption.
      * eapply atomic_step; eassumption.
      * constructor. assumption.
    + now apply IHsnu.
Qed.

Lemma SN_ind_pair (P : term -> term -> Prop):
  (forall t u, (forall t' u', ((t = t' /\ u ~> u') \/ (t ~> t' /\ u = u')) -> P t' u') -> P t u)
    -> forall t u, SN t -> SN u -> P t u.
Proof.
  intros IH t u Hsnt.
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
Lemma enumerate_steps_spec t: forall t', List.In t' (enumerate_steps t) <-> t ~> t'.
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
Lemma enumerate_Forall_beta t : List.Forall (fun t' => t ~> t') (enumerate_steps t).
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
  | cons s (cons t l' as ll) => s ~> t /\ reduction_sequence ll
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
  assert (List.Forall (fun t' => t ~> t' /\ exists n, forall l, reduction_sequence (t' :: l) -> length l <= n) (enumerate_steps t)) as H.
  + pose proof (enumerate_Forall_beta t) as H.
    induction H.
    * constructor.
    * constructor. 2: assumption.
      firstorder.
  + (*Unfortunately, the maximal lengths for all t' are currently hidden underneath existential quantifiers, and not easily accessible.
      We begin by moving them into an existentially quantified list.*)
    assert (exists l', length l' = length (enumerate_steps t) /\ List.Forall (fun (p : prod term nat) => let (t', n) := p in forall l, reduction_sequence (t' :: l) -> length l <= n) (List.combine (enumerate_steps t) l')) as [l' [Hlen Hl']].
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
  - induction n as [| n IHn].
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

Lemma subst_steps t u u': u ~> u' -> t.[u/] ~>* t.[u'/].
Proof.
  intros Hstep.
  apply par_red_to_beta_star.
  apply par_red_subst_par_red.
  2: apply par_red_refl.
  intros [| v].
  - asimpl. now apply beta_to_par_red.
  - asimpl. apply par_red_refl.
Qed.

Lemma SN_inverted_star t t': SN t -> t ~>* t' -> SN t'.
Proof.
  intros Hsn Hsteps.
  induction Hsteps.
  - eapply SN_inverted; eassumption.
  - assumption.
  - firstorder.
Qed.
  

Lemma nested_app_app t inner outer : (nested_app (nested_app t inner) outer) = nested_app t (outer ++ inner).
Proof.
  induction outer as [| t'  outer IH].
  - reflexivity.
  - cbn. rewrite IH. reflexivity.
Qed.

Lemma max_steps_decr t n: (forall l, reduction_sequence (t :: l) -> length l <= n) -> forall t', t ~> t' -> forall l, reduction_sequence (t' :: l) -> length l <= pred n.
Proof.
  intros Hmax t' Hstep.
  destruct n.
  - exfalso.
    specialize (Hmax [t']%list).
    cbn in Hmax. firstorder. lia.
  - cbn.
    intros l.
    specialize (Hmax (t' :: l)%list).
    cbn in Hmax.
    intros Hmx'.
    apply PeanoNat.Nat.succ_le_mono.
    apply Hmax.
    split; assumption.
Qed.

Lemma max_steps_nonzero t t' n: (t ~> t') -> (forall l, reduction_sequence (t :: l) -> length l <= n) -> n > 0.
Proof.
  intros Hstep Hlen.
  specialize (Hlen [t']%list).
  cbn in Hlen. firstorder.
Qed.

Fixpoint update_nth {A : Type} n (l : list A) (a : A) :=
  match l with 
  | nil => nil
  | cons x l' => match n with 
                 | 0 => cons a l'
                 | S n' => cons x (update_nth n' l' a)
                 end
  end.

Lemma update_decr ind n l : ind < length l -> n = List.nth ind l 0 -> n > 0 -> List.list_sum (update_nth ind l (pred n)) < List.list_sum l.
Proof.
  intros Hlen Hind Hgt0.
  induction l as [| x l IH] in ind, Hlen, Hind, Hgt0 |- *.
  - cbn in Hlen. lia.
  - cbn in Hlen.
    destruct ind as [| ind].
    + cbn in *; subst.
      lia.
    + cbn in *. specialize (IH ind).
      apply PeanoNat.lt_S_n in Hlen.
      firstorder. unfold List.list_sum in *. lia.
Qed.

Lemma update_length {A : Type} (l: list A) n v : length (update_nth n l v) = length l.
Proof.
  induction l as [| x l IH] in n |- *.
  - destruct n; reflexivity.
  - destruct n.
    + cbn. reflexivity.
    + cbn. congruence.
Qed.

Lemma max_steps_list_decr t1 t2 l l' outer :
  t1 ~> t2 -> 
  length l' = length (outer ++ t1 :: l) -> 
      List.Forall
        (fun p : prod term nat =>
         let (t, n) := p in
         forall l : list term,
         match l with
         | []%list => True
         | (t0 :: _)%list => t ~> t0 /\ reduction_sequence l
         end -> length l <= n) (List.combine (outer ++ t1 :: l) l') -> 
  exists l'',
  List.list_sum l'' < List.list_sum l'
  /\ length l'' = length (outer ++ t2 :: l)
  /\ List.Forall
  (fun p : prod term nat =>
   let (t0, n) := p in
   forall l0 : list term,
   match l0 with
   | []%list => True
   | (t2 :: _)%list => t0 ~> t2 /\ reduction_sequence l0
   end -> length l0 <= n) (List.combine (outer ++ t2 :: l) l'').
Proof.
  intros Hstep Hlen Hl'.
  pose (length outer) as ind.
  assert (ind < length (outer ++ t1 :: l)) as Hind.
  {
    clear.
    induction outer; cbn in *; lia.
  }
  assert (List.nth ind (outer ++ t1 :: l) (Var 0) = t1) as Hin.
  {
    clear.
    induction outer; cbn in *.
    - reflexivity.
    - assumption.
  }
  rewrite (List.Forall_forall) in Hl'.
  pose (List.nth ind l' 0) as n.
  assert (List.In (t1, n) (List.combine (outer ++ t1 :: l) l')) as H.
  { assert ((t1, n) = List.nth ind (List.combine (outer ++ t1 :: l) l') (Var 0, 0)) as Hnth.
    - rewrite <- Hin.
      rewrite List.combine_nth.
      + repeat f_equal.
        congruence.
      + rewrite Hlen. congruence.
    - rewrite Hnth. apply List.nth_In.
      rewrite List.combine_length.
      lia.
  }
  apply Hl' in H.
  pose proof (max_steps_decr t1 n H t2 Hstep) as Hdecr.
  pose proof (max_steps_nonzero t1 t2 n Hstep H) as Hnz.

  exists (update_nth ind l' (pred n)).
  split. 1: {
    apply update_decr.
    - lia.
    - reflexivity.
    - assumption.
  }
  split. 1: {
    rewrite update_length.
    rewrite Hlen.
    clear.
    induction outer; cbn.
    - reflexivity.
    - congruence.
  }
  rewrite <- List.Forall_forall in Hl'.
  clear - Hdecr Hl' Hlen.
  unfold ind in *.

  induction outer as [| x outer IHouter] in l', Hl', n, Hlen, Hdecr |- *.
  - cbn in *. destruct l'.
    + constructor.
    + constructor.
      * exact Hdecr.
      * inversion Hl'; subst. assumption.
  - destruct l'; cbn in *.
    + congruence.
    + inversion Hl'.
      constructor.
      * assumption.
      * apply IHouter; try assumption.
        now inversion Hlen.
Qed.

(* Lemma 3.2.1 statement (3) for the base case, where the entire term is of some atomic type.
   Formalizing this proof is difficult:
   While intuitively, any reduction step is either within any subterm (not changing the specified shape) or reduction of the leftmost application,
   the main difficulty in Coq stems from the fact that we do not know the size of the term (i.e. the number of applications).

   The current attempt uses the maximal numbers of steps (as determined by max_steps),
   but is stuck at destructing the actual reduction step. Presumably, induction is needed, but I have not yet found a version that yields suitable induction hypotheses.
*)
Lemma base_case t u l : SN (nested_app t.[u/] l) -> SN u -> forall t', nested_app (App (Lam t) u) l ~> t' -> SN t'.
Proof.
  intros Hsn Hsnu.
  (*determine the maximum number of steps for t*)
  assert (exists nt, forall l, reduction_sequence (t :: l) -> length l <= nt) as [nt Hnt].
  { apply max_steps.
    induction l as [| s l IH].
    - eapply SN_subst. 2: reflexivity.
      exact Hsn.
    - apply IH.
      eapply SN_sub_term.
      + exact Hsn.
      + constructor.
  }
  (*determine the maximum number of steps for u*)
  assert (exists nu, forall l, reduction_sequence (u :: l) -> length l <= nu) as [nu Hnu].
  { apply max_steps. assumption. }
  (*determine the maximum number of steps for all terms in l*)
  assert (exists l', length l' = length l /\ List.Forall (fun (p : prod term nat) => let (t, n) := p in forall l, reduction_sequence (t :: l) -> length l <= n) (List.combine l l')) as [l' Hl'].
  { induction l as [| a l IHl].
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
  remember (nt + nu + List.list_sum l') as n eqn:Heqn.
  (*We do induction on n with everything else quantified.*)
  induction n as [n IH] using nat_strong_ind in t, u, l, Hsn, Hsnu, nt, Hnt, nu, Hnu, l', Hl', Heqn |- *.
  intros t' Hstep.

  change l with (app nil l) in *.
  change (SN (nested_app t' nil)).
  cbn in Hstep.
  remember nil as outer.
  
  remember (nested_app (App (Lam t) u) l) as trm eqn:Heqtrm.
  induction Hstep as [| ta tb tc Hstep IHstep | ta tb tc Hstep IHstep | ta tb Hstep IHstep] in t, u, l, outer, Hsn, Hsnu, nt, Hnt, nu, Hnu, l', Hl', Heqn, Heqtrm |- *.
  - subst.
    destruct l as [| ? l].
    + cbn in Heqtrm. inversion Heqtrm; subst. rewrite List.app_nil_r in Hsn. assumption.
    + cbn in Heqtrm. inversion Heqtrm; subst.
      destruct l; cbn in *; congruence.
  - subst.
    destruct l as [| t1 l]; cbn in *.
    + inversion Heqtrm; subst.
      inversion Hstep as [| | | H1 H2 Hstep' H3 H4]; subst.
      constructor. eapply IH.
      3, 5: eassumption.
      5: reflexivity.
      4: rewrite List.app_nil_r in Hl'; exact Hl'.
      3: apply (max_steps_decr t); eassumption.
      1: apply (max_steps_nonzero t _ nt) in Hstep'.
      1: lia.
      1: assumption.
      clear - Hsn Hstep'.
      eapply SN_inverted. 1: exact Hsn.
      induction outer as [| a outer IHouter].
      * cbn. now apply beta_subst.
      * cbn. constructor. 
        apply IHouter.
        eapply SN_sub_term. 1: exact Hsn.
        cbn. constructor.
    + change (App tb tc) with (nested_app tb [tc]).
      rewrite nested_app_app.
      inversion Heqtrm; subst.
      eapply IHstep.
      2: exact Hsnu.
      2: exact Hnt.
      2: exact Hnu.
      3, 4: reflexivity.
      1, 2: assert ((outer ++ [t1]) ++ l = outer ++ (t1 :: l))%list as -> by (rewrite <- List.app_assoc; reflexivity).
      all: assumption.
  - destruct l as [| t1 l]; cbn in *.
    + inversion Heqtrm; subst.
      constructor. eapply IH.
      7: reflexivity.
      6: rewrite List.app_nil_r in Hl'; exact Hl'.
      3: now apply (SN_inverted u).
      3: eassumption.
      3: apply (max_steps_decr u); eassumption.
      1: apply (max_steps_nonzero u _ nu) in Hstep.
      1: lia.
      1: assumption.
      clear - Hsn Hsnu Hstep.
      eapply SN_inverted_star. 1: exact Hsn.
      induction outer as [| a outer IHouter].
      * cbn. now apply subst_steps.
      * cbn. apply beta_star_app. 2: apply beta_star_refl.
        apply IHouter.
        eapply SN_sub_term. 1: exact Hsn.
        cbn. constructor.
    + inversion Heqtrm; subst.
      change (SN (nested_app (nested_app (App (Lam t) u) (tc :: l)) outer)).
      rewrite (nested_app_app).
      destruct Hl' as [Hl'1 Hl'2].
      pose proof (max_steps_list_decr t1 tc l l' outer Hstep Hl'1 Hl'2) as (l'' & Hdecr & Hl'').
      constructor.
      eapply IH.
      3: exact Hsnu.
      3: exact Hnt.
      3: exact Hnu.
      4: reflexivity.
      3: exact Hl''.
      1: lia.
      eapply SN_inverted. 1: exact Hsn.
      clear - Hstep.
      induction outer; now constructor.
  - destruct l; cbn in Heqtrm; congruence.
Qed.

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
