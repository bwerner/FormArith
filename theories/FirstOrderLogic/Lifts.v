(**
  This file is not the most interesting one of this section: it handles all the
  required work to make the term and formula lifts correct.
*)

From FormArith.FirstOrderLogic Require Import Definitions.

Require Import Lia.

(** * Lifts *)

(** ** Definitions *)

(** *** Lifts *)

(**
  Lifts a term [t] by [up_idx] until index [until_idx].

  This means that all the variables ([nat]) in [t] that are below
  [until_idx] will be increased by [up_idx].
*)
Fixpoint term_lift (until_idx up_idx: nat) (t: term): term :=
  match t with
  | TVar idx => if (idx <? until_idx) then t else TVar (idx + up_idx)
  | TApp fct_idx terms => TApp fct_idx (map (term_lift until_idx up_idx) terms)
  end.

(** Lifts a formula with the same principle as [term_lift]. *)
Fixpoint formula_lift (until_idx up_idx: nat) (phi: formula): formula :=
  match phi with
  | FAtom pred_idx terms => FAtom pred_idx (map (term_lift until_idx up_idx) terms)

  | FConj phi phi' => FConj (formula_lift until_idx up_idx phi) (formula_lift until_idx up_idx phi')
  | FDisj phi phi' => FDisj (formula_lift until_idx up_idx phi) (formula_lift until_idx up_idx phi')
  | FImp phi phi' => FImp (formula_lift until_idx up_idx phi) (formula_lift until_idx up_idx phi')

  | FBot => phi
  | FTop => phi

  | FForAll phi => FForAll (formula_lift (S until_idx) up_idx phi)
  | FExists phi => FExists (formula_lift (S until_idx) up_idx phi)
  end.

(** Lifts every formula in a context. *)
Fixpoint context_lift (until_idx up_idx: nat) (delta: list formula) :=
  match delta with
  | nil => delta
  | phi :: delta => (formula_lift until_idx up_idx phi) :: (context_lift until_idx up_idx delta)
  end.

(** *** Substitutions *)

(**
  Substitutes a variable by a term in a term.

  This function will replace every occurence of [change_idx] in [t] by
  [change_idx].
*)
Fixpoint term_subst (change_idx: nat) (new_term: term) (t: term): term :=
  match t with
  | TVar idx =>
      if (change_idx =? idx) then new_term else
        if (change_idx <? idx) then TVar (idx - 1) else TVar idx
  | TApp fct_idx terms => TApp fct_idx (map (term_subst change_idx new_term) terms)
  end.

(** Substitutes a variable by a term in a formula using [term_subst]. *)
Fixpoint formula_subst (change_idx: nat) (new_term: term) (phi: formula): formula :=
  match phi with
  | FAtom pred_idx terms => FAtom pred_idx (map (term_subst change_idx new_term) terms)

  | FConj phi phi' => FConj (formula_subst change_idx new_term phi) (formula_subst change_idx new_term phi')
  | FDisj phi phi' => FDisj (formula_subst change_idx new_term phi) (formula_subst change_idx new_term phi')
  | FImp phi phi' => FImp (formula_subst change_idx new_term phi) (formula_subst change_idx new_term phi')

  | FBot => phi
  | FTop => phi

  | FForAll phi => FForAll (formula_subst (S change_idx) (term_lift 0 1 new_term) phi)
  | FExists phi => FExists (formula_subst (S change_idx) (term_lift 0 1 new_term) phi)
  end.


(** ** Properties *)

(** *** Lifts *)

Ltac solve_TApp_case terms IHterms :=
  let IHAppTerms := fresh "IHAppTerms" in

  induction terms as [| ? ? IHAppTerms ]; simpl; [ reflexivity |];
  f_equal; [ apply Forall_inv in IHterms | apply IHAppTerms; eapply Forall_inv_tail ]; eauto.

Lemma term_lift_0 (t: term) (idx: nat):
  term_lift idx 0 t = t.
Proof.
  induction t as [ n | ? terms IHterms ]; simpl.
  2: { f_equal; solve_TApp_case terms IHterms. }

  destruct (PeanoNat.Nat.ltb_spec n idx).
  - reflexivity.
  - f_equal; lia.
Qed.

Lemma term_lift_0_lift_0 (t: term) (idx idx': nat):
  term_lift 0 idx (term_lift 0 idx' t) = term_lift 0 (idx + idx') t.
Proof.
  induction t as [| ? terms IHterms ]; simpl.
  2: { f_equal; solve_TApp_case terms IHterms. }

  f_equal; lia.
Qed.

Lemma term_lift_S_lift_0 (t: term) (idx: nat):
  term_lift (S idx) 1 (term_lift 0 1 t) = term_lift 0 1 (term_lift idx 1 t).
Proof.
  induction t as [ n | ? terms IHterms ]; simpl.
  2: { f_equal; solve_TApp_case terms IHterms. }

  destruct (PeanoNat.Nat.ltb_spec (n + 1) (S idx)), (PeanoNat.Nat.ltb_spec n idx);
    (reflexivity || lia).
Qed.

Lemma term_lift_S_lift_n (t: term) (idx idx': nat):
  term_lift (S (idx + idx')) 1 (term_lift idx 1 t) =
    term_lift idx 1 (term_lift (idx + idx') 1 t).
Proof.
  induction t as [ n | ? terms IHterms ]; simpl.
  2: { f_equal; solve_TApp_case terms IHterms. }

  destruct (PeanoNat.Nat.ltb_spec n idx), (PeanoNat.Nat.ltb_spec n (idx + idx')).
  all: destruct (PeanoNat.Nat.ltb_spec n idx), (PeanoNat.Nat.ltb_spec n (S (idx + idx'))); simpl.
  all: destruct (PeanoNat.Nat.ltb_spec n idx), (PeanoNat.Nat.ltb_spec n (S (idx + idx'))).
  all: destruct (PeanoNat.Nat.ltb_spec (n + 1) idx), (PeanoNat.Nat.ltb_spec (n + 1) (S (idx + idx'))).
  all: reflexivity || lia.
Qed.

Lemma term_lift_n_lift_n (t: term) (idx idx' idx'': nat):
  term_lift idx idx' (term_lift idx idx'' t) = term_lift idx (idx' + idx'') t.
Proof.
  induction t as [ n | ? terms IHterms ]; simpl.
  2: { f_equal; solve_TApp_case terms IHterms. }

  destruct (PeanoNat.Nat.ltb_spec n idx); simpl.
  - destruct (PeanoNat.Nat.ltb_spec n idx); [| lia ].
    reflexivity.

  - destruct (PeanoNat.Nat.ltb_spec (n + idx'') idx); [ lia |].
    f_equal; lia.
Qed.

Lemma term_lift_S_lift_0_iter (idx: nat) (terms: list term):
  map (term_lift (S idx) 1) (map (term_lift 0 1) terms) =
    map (term_lift 0 1) (map (term_lift idx 1) terms).
Proof.
  induction terms; simpl.
  { reflexivity. }

  rewrite term_lift_S_lift_0.
  f_equal; assumption.
Qed.

Lemma term_lift_S_lift_n_iter (idx idx': nat) (terms: list term):
  map (term_lift (S (idx + idx')) 1) (map (term_lift idx 1) terms) =
    map (term_lift idx 1) (map (term_lift (idx + idx') 1) terms).
Proof.
  induction terms; simpl.
  { reflexivity. }

  rewrite term_lift_S_lift_n.
  f_equal; assumption.
Qed.

Lemma term_lift_n_lift_n_iter (idx idx' idx'': nat) (terms: list term):
  map (term_lift idx idx') (map (term_lift idx idx'') terms) =
    map (term_lift idx (idx' + idx'')) terms.
Proof.
  induction terms; simpl.
  { reflexivity. }

  rewrite term_lift_n_lift_n.
  f_equal; assumption.
Qed.

Lemma formula_lift_S_lift_n (phi: formula) (idx idx': nat):
  formula_lift (S (idx + idx')) 1 (formula_lift idx 1 phi) =
    formula_lift idx 1 (formula_lift (idx + idx') 1 phi).
Proof.
  generalize idx.

  induction phi as [ | ? IHphi1 ? IHphi2 | ? IHphi1 ? IHphi2 | ? IHphi1 ? IHphi2 | | | ? IHphi | ? IHphi ];
    simpl; intros.

  (* FAtom *)
  - rewrite term_lift_S_lift_n_iter.
    reflexivity.

  (* FConj, FDisj, FImp *)
  - f_equal; [ apply IHphi1 | apply IHphi2 ].
  - f_equal; [ apply IHphi1 | apply IHphi2 ].
  - f_equal; [ apply IHphi1 | apply IHphi2 ].

  (* FBot, FTop *)
  - reflexivity.
  - reflexivity.

  (* FForAll, FExists *)
  - rewrite <- PeanoNat.Nat.add_succ_l.
    f_equal; apply IHphi.
  - rewrite <- PeanoNat.Nat.add_succ_l.
    f_equal; apply IHphi.
Qed.

Lemma formula_lift_n_lift_n (phi: formula) (idx idx' idx'': nat):
  formula_lift idx idx' (formula_lift idx idx'' phi) =
    formula_lift idx (idx' + idx'') phi.
Proof.
  generalize idx idx'.

  induction phi as [ ? terms | ? IHphi1 ? IHphi2 | ? IHphi1 ? IHphi2 | ? IHphi1 ? IHphi2 | | | ? IHphi | ? IHphi ];
    simpl; intros.

  (* FAtom *)
  - f_equal; apply term_lift_n_lift_n_iter.

  (* FConj, FDisj, FImp *)
  - f_equal; [ apply IHphi1 | apply IHphi2 ].
  - f_equal; [ apply IHphi1 | apply IHphi2 ].
  - f_equal; [ apply IHphi1 | apply IHphi2 ].

  (* FBot, FTop *)
  - reflexivity.
  - reflexivity.

  (* FForAll, FExists *)
  - f_equal; apply IHphi.
  - f_equal; apply IHphi.
Qed.

Lemma formula_lift_nth (gamma: list formula) (n idx idx': nat):
  nth n (context_lift idx idx' gamma) FTop = formula_lift idx idx' (nth n gamma FTop).
Proof.
  generalize n.

  induction gamma as [| ? ? IHgamma ]; simpl.
  { intros []; reflexivity. }

  intros [].
  - reflexivity.
  - apply IHgamma.
Qed.

Lemma context_lift_0_lift_0 (gamma: list formula) (idx idx': nat):
  context_lift 0 idx (context_lift 0 idx' gamma) = context_lift 0 (idx + idx') gamma.
Proof.
  induction gamma as [| ? ? IHgamma ]; simpl.
  { reflexivity. }

  f_equal.
  - rewrite formula_lift_n_lift_n.
    reflexivity.
  - apply IHgamma.
Qed.

Lemma context_lift_S_lift_n (gamma: list formula) (idx idx': nat):
  context_lift (S (idx + idx')) 1 (context_lift idx 1 gamma) =
    context_lift idx 1 (context_lift (idx + idx') 1 gamma).
Proof.
  induction gamma as [| ? ? IHgamma ]; simpl.
  { reflexivity. }

  f_equal.
  - rewrite formula_lift_S_lift_n.
    reflexivity.
  - apply IHgamma.
Qed.

Lemma context_lift_app (gamma gamma': list formula) (idx idx': nat):
  context_lift idx idx' gamma ++ context_lift idx idx' gamma' =
    context_lift idx idx' (gamma ++ gamma').
Proof.
  induction gamma as [| ? ? IHgamma ]; simpl.
  { reflexivity. }

  rewrite IHgamma.
  reflexivity.
Qed.

(** *** Substitutions *)

Lemma term_subst_lift (t new_term: term) (idx: nat):
  term_subst idx new_term (term_lift idx 1 t) = t.
Proof.
  induction t as [ n | ? terms IHterms ]; simpl.
  2: { f_equal; solve_TApp_case terms IHterms. }

  destruct (PeanoNat.Nat.ltb_spec n idx); simpl.
  - destruct (PeanoNat.Nat.eqb_spec idx n); [ lia |].
    destruct (PeanoNat.Nat.ltb_spec idx n); [ lia |].
    intros; reflexivity.

  - destruct (PeanoNat.Nat.eqb_spec idx (n + 1)); [ lia |].
    destruct (PeanoNat.Nat.ltb_spec idx (n + 1)); [| lia ].
    f_equal; lia.
Qed.

Lemma term_subst_lift_iter (terms: list term) (new_term: term) (idx: nat):
  map (term_subst idx new_term) (map (term_lift idx 1) terms) = terms.
Proof.
  induction terms as [| ? ? IHterms ]; simpl.
  { reflexivity. }

  f_equal.
  - apply term_subst_lift.
  - apply IHterms.
Qed.

Lemma term_subst_lift_S (t new_term: term) (idx idx': nat):
  term_subst idx (term_lift (idx + idx') 1 new_term) (term_lift (S (idx + idx')) 1 t) =
    term_lift (idx + idx') 1 (term_subst idx new_term t).
Proof.
  induction t as [ n | ? terms IHterms ]; simpl.
  2: { f_equal; solve_TApp_case terms IHterms. }

  destruct (PeanoNat.Nat.ltb_spec n (S (idx + idx'))); simpl.
  - destruct (PeanoNat.Nat.eqb_spec idx n); [ reflexivity |].
    destruct (PeanoNat.Nat.ltb_spec idx n); simpl.
    + destruct (PeanoNat.Nat.ltb_spec (n - 1) (idx + idx')); [| lia ].
      reflexivity.
    + destruct (PeanoNat.Nat.ltb_spec n (idx + idx')); [| lia ].
      reflexivity.

  - destruct (PeanoNat.Nat.eqb_spec idx (n + 1)); [ lia |].
    destruct (PeanoNat.Nat.ltb_spec idx (n + 1)); [| lia ].
    destruct (PeanoNat.Nat.eqb_spec idx n); [ lia |].
    destruct (PeanoNat.Nat.ltb_spec idx n); simpl; [| lia ].
    destruct (PeanoNat.Nat.ltb_spec (n - 1) (idx + idx')); [ lia |].
    f_equal; lia.
Qed.

Lemma term_subst_lift_S_iter (terms: list term) (new_term: term) (idx idx': nat):
  map (term_subst idx (term_lift (idx + idx') 1 new_term)) (map (term_lift (S (idx + idx')) 1) terms) =
    map (term_lift (idx + idx') 1) (map (term_subst idx new_term) terms).
Proof.
  induction terms as [| ? ? IHterms ]; simpl.
  { reflexivity. }

  rewrite term_subst_lift_S.
  f_equal; assumption.
Qed.

(** *** Evaluations *)

Lemma term_eval_lift_n (fcts: nat -> list nat -> nat) (σ σ': list nat) (idx: nat) (t: term):
  term_eval fcts (σ ++ (idx :: σ')) (term_lift (length σ) 1 t) =
    term_eval fcts (σ ++ σ') t.
Proof.
  induction t as [ idx' | ? terms IHterms ]; simpl.
  - destruct (PeanoNat.Nat.ltb_spec idx' (length σ)); simpl.
    + rewrite !app_nth1 by assumption.
      reflexivity.

    + rewrite !app_nth2 by lia.
      replace (idx' + 1) with (S idx') by lia.
      rewrite PeanoNat.Nat.sub_succ_l by assumption.
      simpl; lia.

  - replace (map _ _) with (map (term_eval fcts (σ ++ σ')) terms); [ reflexivity |].
    solve_TApp_case terms IHterms.
Qed.

Lemma term_eval_lift_0 (fcts: nat -> list nat -> nat) (σ σ': list nat) (t: term):
  term_eval fcts σ t = term_eval fcts (σ' ++ σ) (term_lift 0 (length σ') t).
Proof.
  induction t as [ idx | ? terms IHterms ]; simpl.
  - rewrite app_nth2 by lia.
    replace (idx + _ - _) with idx by lia.
    reflexivity.

  - replace (map _ (map _ _)) with (map (term_eval fcts σ) terms); [ reflexivity |].
    solve_TApp_case terms IHterms.
Qed.

Lemma term_eval_lift_n_iter (fcts: nat -> list nat -> nat)
    (σ σ': list nat) (idx: nat) (terms: list term):
  map (term_eval fcts (σ ++ idx :: σ')) (map (term_lift (length σ) 1) terms) =
    map (term_eval fcts (σ ++ σ')) terms.
Proof.
  induction terms; simpl.
  { reflexivity. }

  rewrite term_eval_lift_n.
  f_equal; assumption.
Qed.

Lemma term_eval_subst_lift (fcts: nat -> list nat -> nat) (σ σ': list nat) (t t': term):
  term_eval fcts (σ ++ σ') (term_subst (length σ) (term_lift 0 (length σ) t') t)
    = term_eval fcts (σ ++ (term_eval fcts σ' t') :: σ') t.
Proof.
  induction t as [ idx | ? terms IHterms ]; simpl.
  2: { f_equal; solve_TApp_case terms IHterms. }

  destruct (PeanoNat.Nat.eqb_spec (length σ) idx) as [ Heq |]; simpl.
  { rewrite <- Heq.
    rewrite nth_middle.
    rewrite <- term_eval_lift_0.
    reflexivity. }

  destruct (PeanoNat.Nat.ltb_spec (length σ) idx) as [ Heq |]; simpl.
  { destruct idx; [ lia |]; simpl.
    rewrite PeanoNat.Nat.sub_0_r.
    rewrite !app_nth2; [| lia.. ].
    rewrite PeanoNat.Nat.sub_succ_l; [| lia ]; simpl.
    reflexivity. }

  rewrite !app_nth1; [| lia.. ].
  reflexivity.
Qed.

Lemma formula_subst_lift (phi: formula) (change_idx: nat) (new_term: term):
  formula_subst change_idx new_term (formula_lift change_idx 1 phi) = phi.
Proof.
  generalize new_term change_idx.

  induction phi as [ | ? IHphi1 ? IHphi2 | ? IHphi1 ? IHphi2 | ? IHphi1 ? IHphi2 | | | ? IHphi | ? IHphi ];
    simpl; intros.

  (* FAtom *)
  - rewrite term_subst_lift_iter.
    reflexivity.

  (* FConj, FDisj, FImp *)
  - f_equal; [ apply IHphi1 | apply IHphi2 ].
  - f_equal; [ apply IHphi1 | apply IHphi2 ].
  - f_equal; [ apply IHphi1 | apply IHphi2 ].

  (* FBot, FTop *)
  - reflexivity.
  - reflexivity.

  (* FForAll, FExists *)
  - f_equal; apply IHphi.
  - f_equal; apply IHphi.
Qed.

Lemma formula_subst_lift_lift (phi: formula) (idx idx': nat) (new_term: term):
  formula_subst idx (term_lift (idx + idx') 1 new_term) (formula_lift (S (idx + idx')) 1 phi) =
    formula_lift (idx + idx') 1 (formula_subst idx new_term phi).
Proof.
  generalize idx idx' new_term.

  induction phi as [ | ? IHphi1 ? IHphi2 | ? IHphi1 ? IHphi2 | ? IHphi1 ? IHphi2 | | | ? IHphi | ? IHphi ];
    simpl; intros idx'' idx''' new_term'.

  (* FAtom *)
  - rewrite term_subst_lift_S_iter.
    reflexivity.

  (* FConj, FDisj, FImp *)
  - f_equal; [ apply IHphi1 | apply IHphi2 ].
  - f_equal; [ apply IHphi1 | apply IHphi2 ].
  - f_equal; [ apply IHphi1 | apply IHphi2 ].

  (* FBot, FTop *)
  - reflexivity.
  - reflexivity.

  (* FForAll *)
  - f_equal.
    replace (S (idx'' + idx''')) with ((S idx'') + idx''') by lia.
    rewrite <- IHphi.
    rewrite <- term_lift_S_lift_0.
    reflexivity.

  (* FExists *)
  - f_equal.
    replace (S (idx'' + idx''')) with ((S idx'') + idx''') by lia.
    rewrite <- IHphi.
    rewrite <- term_lift_S_lift_0.
    reflexivity.
Qed.

Lemma formula_eval_S (fcts: nat -> list nat -> nat) (preds: nat -> list nat -> Prop)
    (phi: formula) (σ σ': list nat) (idx: nat):
  formula_eval fcts preds (σ ++ idx :: σ') (formula_lift (length σ) 1 phi) <->
    formula_eval fcts preds (σ ++ σ') phi.
Proof.
  generalize σ.

  induction phi as [ | ? IHphi1 ? IHphi2 | ? IHphi1 ? IHphi2 | ? IHphi1 ? IHphi2 | | | ? IHphi | ? IHphi ];
    simpl; intros σ''.

  (* FAtom *)
  - rewrite term_eval_lift_n_iter.
    reflexivity.

  (* FConj *)
  - split; intros [].
    + split; [ apply IHphi1 | apply IHphi2 ]; assumption.
    + split; [ apply IHphi1 | apply IHphi2 ]; assumption.

  (* FDisj *)
  - split; intros [];
      [ left | right | left | right ];
      [ apply IHphi1 | apply IHphi2 | apply IHphi1 | apply IHphi2 ];
      assumption.

  (* FImp *)
  - split.
    all: intros Hphi ?.
    all: apply IHphi2, Hphi, IHphi1.
    all: assumption.

  (* FBot, FTop *)
  - reflexivity.
  - reflexivity.

  (* FForAll *)
  - split; intros Hphi x.
    all: apply (IHphi (x :: σ'')).
    all: apply Hphi.

  (* FExists *)
  - split; intros [x Heval].
    all: exists x.
    all: apply (IHphi (x :: σ'')).
    all: apply Heval.
Qed.

Lemma formula_eval_subst_lift (fcts: nat -> list nat -> nat) (preds: nat -> list nat -> Prop)
    (phi: formula) (σ σ': list nat) (t: term):
  formula_eval fcts preds (σ ++ σ') (formula_subst (length σ) (term_lift 0 (length σ) t) phi)
    <-> formula_eval fcts preds (σ ++ (term_eval fcts σ' t) :: σ') phi.
Proof.
  generalize σ.

  induction phi as [ ? terms | ? IHphi1 ? IHphi2 | ? IHphi1 ? IHphi2 | ? IHphi1 ? IHphi2 | | | ? IHphi | ? IHphi ];
    simpl; intros σ''.

  (* FAtom *)
  - replace (map _ _) with (map (term_eval fcts (σ'' ++ term_eval fcts σ' t :: σ')) terms); [ reflexivity |].
    induction terms as [| ? ? IHterms ]; simpl.
    { reflexivity. }

    f_equal.
    + rewrite term_eval_subst_lift.
      reflexivity.
    + apply IHterms.

  (* FConj *)
  - split; intros [].
    + split; [ apply IHphi1 | apply IHphi2 ]; assumption.
    + split; [ apply IHphi1 | apply IHphi2 ]; assumption.

  (* FDisj *)
  - split; intros [];
      [ left | right | left | right ];
      [ apply IHphi1 | apply IHphi2 | apply IHphi1 | apply IHphi2 ];
      assumption.

  (* FImp *)
  - split.
    all: intros Hphi ?.
    all: apply IHphi2, Hphi, IHphi1.
    all: assumption.

  (* FBot, FTop *)
  - reflexivity.
  - reflexivity.

  (* FForAll *)
  - split; intros Hphi x; simpl.
    + apply (IHphi (x :: σ'')).
      replace (term_lift _ _ _) with (term_lift 0 1 (term_lift 0 (length σ'') t)).
      { apply Hphi. }

      rewrite term_lift_0_lift_0.
      reflexivity.

    + specialize (IHphi (x :: σ'')).
      rewrite term_lift_0_lift_0.
      apply IHphi.
      apply Hphi.

  (* FExists *)
  - split; intros [x Hphi]; exists x; simpl.
    + apply (IHphi (x :: σ'')).
      replace (term_lift _ _ _) with (term_lift 0 1 (term_lift 0 (length σ'') t)).
      { apply Hphi. }

      rewrite term_lift_0_lift_0.
      reflexivity.

    + specialize (IHphi (x :: σ'')).
      rewrite term_lift_0_lift_0.
      apply IHphi.
      apply Hphi.
Qed.
