(**
  This file defines derivations in the first-order logic with some weakening properties.
*)

From FormArith.FirstOrderLogic Require Import Definitions Lifts.

Require Import Lia.

(** * Derivations *)

(** ** Rules of the first-order logic

  [Derivable Γ φ] should be read as "The formula ϕ is derivable under the
  context Γ".
*)
Inductive Derivable: list formula -> formula -> Type :=
  (** A ∈ Γ ⇒ Γ ⊢ A *)
  | RAxiom (gamma: list formula) (idx: nat):
      Derivable gamma (nth idx gamma FTop)

  (** Γ ⊢ ⊤ *)
  | RTop_i (gamma: list formula):
      Derivable gamma FTop

  (** Γ ⊢ ⊥ ⇒ Γ ⊢ A  *)
  | RBot_e (gamma: list formula) (phi: formula):
      Derivable gamma FBot -> Derivable gamma phi

  (** Γ, φ ⊢ ψ ⇒ Γ ⊢ φ → ψ *)
  | RImp_i (gamma: list formula) (phi phi': formula):
      Derivable (phi :: gamma) phi' -> Derivable gamma (FImp phi phi')

  (** (Γ ⊢ φ) ∧ (Γ ⊢ φ) → ψ ⇒ Γ ⊢ ψ *)
  | RImp_e (gamma: list formula) (phi phi': formula):
      Derivable gamma phi -> Derivable gamma (FImp phi phi') -> Derivable gamma phi'

  (** (Γ ⊢ φ) ∧ (Γ ⊢ ψ) ⇒ Γ ⊢ φ ∧ ψ *)
  | RConj_i (gamma: list formula) (phi phi': formula):
      Derivable gamma phi -> Derivable gamma phi' -> Derivable gamma (FConj phi phi')

  (** Γ ⊢ φ ∧ ψ ⇒ Γ ⊢ φ *)
  | RConj_e1 (gamma: list formula) (phi phi': formula):
      Derivable gamma (FConj phi phi') -> Derivable gamma phi

  (** Γ ⊢ φ ∧ ψ ⇒ Γ ⊢ ψ *)
  | RConj_e2 (gamma: list formula) (phi phi': formula):
      Derivable gamma (FConj phi phi') -> Derivable gamma phi'

  (** Γ ⊢ φ ⇒ Γ ⊢ φ ∨ ψ *)
  | RDisj_i1 (gamma: list formula) (phi phi': formula):
      Derivable gamma phi -> Derivable gamma (FDisj phi phi')

  (** Γ ⊢ ψ ⇒ Γ ⊢ φ ∨ ψ *)
  | RDisj_i2 (gamma: list formula) (phi phi': formula):
      Derivable gamma phi' -> Derivable gamma (FDisj phi phi')

  (** (Γ ⊢ φ ∨ ψ) ∧ (Γ, φ ⊢ θ) ∧ (Γ, ψ ⊢ θ) ⇒ Γ ⊢ θ*)
  | RDisj_e (gamma: list formula) (phi phi' phi'': formula):
      Derivable gamma (FDisj phi phi') ->
      Derivable (phi :: gamma) phi'' -> Derivable (phi' :: gamma) phi'' ->
      Derivable gamma phi''

  (** ⇑Γ ⊢ φ ⇒ Γ ⊢ ∀ φ *)
  | RForAll_i (gamma: list formula) (phi: formula):
      Derivable (context_lift 0 1 gamma) phi -> Derivable gamma (FForAll phi)

  (** Γ ⊢ ∀ φ ⇒ Γ ⊢ φ[[0 ← t]] *)
  | RForAll_e (gamma: list formula) (phi: formula) (t: term):
      Derivable gamma (FForAll phi) -> Derivable gamma (formula_subst 0 t phi)

  (** Γ ⊢ φ[[0 ← t]] ⇒ Γ ⊢ ∃ φ *)
  | RExists_i (gamma: list formula) (phi: formula) (t: term):
      Derivable gamma (formula_subst 0 t phi) -> Derivable gamma (FExists phi)

  (** (Γ ⊢ ∃ φ) ∧ (⇑Γ, φ ⊢ ⇑ψ) ⇒ Γ ⊢ ψ *)
  | RExists_e (gamma: list formula) (phi phi': formula):
      Derivable gamma (FExists phi) ->
      Derivable (phi :: context_lift 0 1 gamma) (formula_lift 0 1 phi') ->
      Derivable gamma phi'.


(** ** Correction *)

(**
  This lemma states that if Γ ⊢ φ in our representation of the first-order
  logic, then it also holds in Rocq [Prop].
*)
Lemma derivable_correctness (fcts: nat -> list nat -> nat) (preds: nat -> list nat -> Prop)
    (gamma: list formula) (phi: formula):
  Derivable gamma phi ->
    forall (σ: list nat),
      (forall (idx: nat), formula_eval fcts preds σ (nth idx gamma FTop)) ->
        formula_eval fcts preds σ phi.
Proof.
  induction 1 as
    [ | | ? ? _ IHind |
      (* RImp *)  ? ? ? _ IHind | ? ? ? _ IHind1 _ IHind2 |
      (* RConj *) ? ? ? _ IHind1 _ IHind2 | ? ? ? _ IHind | ? ? ? _ IHind |
      (* RDisj *) ? ? ? _ IHind | ? ? ? _ IHind | ? ? ? ? _ IHind1 _ IHind2 _ IHind3 |
      (* RForAll *) ? ? _ IHind | ? ? phi _ IHind |
      (* RExists *) ? ? phi _ IHind | ? ? ? _ IHind1 _ IHind2 ];
    simpl in *; intros σ IHtree; intros.

  (* RAxiom *)
  - apply IHtree.

  (* RTop_i *)
  - exact I.

  (* RBot_e *)
  - exfalso.
    apply (IHind σ).
    apply IHtree.

  (* RImp_i *)
  - apply (IHind σ).
    intros [|].
    + assumption.
    + apply IHtree.

  (* RImp_e *)
  - apply IHind2.
    + apply IHtree.
    + apply IHind1.
      apply IHtree.

  (* RConj_i *)
  - split.
    + apply IHind1.
      apply IHtree.
    + apply IHind2.
      apply IHtree.

  (* RConj_e1 *)
  - apply IHind.
    apply IHtree.

  (* RConj_e2 *)
  - apply IHind.
    apply IHtree.

  (* RDisj_i1 *)
  - left.
    apply IHind.
    apply IHtree.

  (* RDisj_i2 *)
  - right.
    apply IHind.
    apply IHtree.

  (* RDisj_e *)
  - destruct (IHind1 σ IHtree).
    + apply IHind2.
      intros [|]; [ assumption | apply IHtree ].
    + apply IHind3.
      intros [|]; [ assumption | apply IHtree ].

  (* RForAll_i *)
  - apply IHind; intros n.
    rewrite formula_lift_nth.
    apply formula_eval_S with (σ := nil).
    apply IHtree.

  (* RForAll_e *)
  - rewrite <- (term_lift_0 phi 0).
    apply formula_eval_subst_lift with (σ := nil).
    apply IHind.
    apply IHtree.

  (* RExists_i *)
  - exists (term_eval fcts σ phi).
    apply formula_eval_subst_lift with (σ := nil).
    rewrite term_lift_0.
    apply IHind.
    apply IHtree.

  (* RExists_e *)
  - destruct (IHind1 σ IHtree) as [ n ? ].
    apply formula_eval_S with (σ := nil) (idx := n).
    apply IHind2.

    intros [|]; [ assumption |].
    rewrite formula_lift_nth.
    apply formula_eval_S with (σ := nil).
    apply IHtree.
Qed.

(** ** Weakening lemmas  *)

(** Small auxiliary lemma to prove [derivable_weak']. *)
Lemma app_cons_nil {T: Type} (l l': list T) (x: T):
  (l ++ x :: nil) ++ l' = l ++ x :: l'.
Proof.
  induction l as [| ? ? IHl ]; simpl.
  { reflexivity. }

  rewrite IHl.
  reflexivity.
Qed.

(** (Γ ⊢ φ) ∧ (Γ = Γ', Γ'') ⇒ Γ', ψ, Γ'' ⊢ φ *)
Lemma derivable_weak' (gamma: list formula) (phi: formula):
  Derivable gamma phi ->
    forall (gamma' gamma'': list formula) (phi': formula),
      gamma = gamma' ++ gamma'' -> Derivable (gamma' ++ phi' :: gamma'') phi.
Proof.
  induction 1 as
    [ ? idx | | ? ? _ IHind |
      (* RImp *)  ? ? ? _ IHind | ? A B _ IHind1 _ IHind2 |
      (* RConj *) ? ? ? _ IHind1 _ IHind2 | ? A B _ IHind | ? A B _ IHind |
      (* RDisj *) ? ? ? _ IHind | ? ? ? _ IHind | ? A B C _ IHind1 _ IHind2 _ IHind3 |
      (* RForAll *) ? ? _ IHind | ? ? ? _ IHind |
      (* RExists *) ? ? phi _ IHind | ? phi ? _ IHind1 _ IHind2 ];
    simpl in *; intros gamma' gamma'' phi'' ->.

  (* RAxiom *)
  - destruct (PeanoNat.Nat.ltb_spec0 idx (length gamma')).
    { generalize (RAxiom (gamma' ++ phi'' :: gamma'') idx).
      rewrite !app_nth1; [| lia.. ].
      intros; assumption. }

    replace (nth _ _ _) with (nth (S idx) ((gamma' ++ phi'' :: nil) ++ gamma'') FTop).
    { rewrite app_cons_nil. apply RAxiom. }

    destruct (PeanoNat.Nat.ltb_spec0 (S idx) (length (gamma' ++ phi'' :: nil))) as [ Heq |].
    { rewrite app_length in Heq; simpl in Heq.
      lia. }

    rewrite !app_nth2; [| lia.. ].
    rewrite app_length.

    f_equal.
    replace (length (_ :: nil)) with 1 by reflexivity.
    lia.

  (* RTop_i *)
  - apply RTop_i.

  (* RBot_e *)
  - apply RBot_e.
    apply IHind.
    reflexivity.

  (* RImp_i *)
   - apply RImp_i.
     rewrite app_comm_cons.
     apply IHind.
     reflexivity.

  (* RImp_e *)
   - apply RImp_e with A.
     + apply IHind1.
       reflexivity.
     + apply IHind2.
       reflexivity.

  (* RConj_i *)
  - apply RConj_i.
    + apply IHind1.
      reflexivity.
    + apply IHind2.
      reflexivity.

  (* RConj_e1 *)
  - apply RConj_e1 with B.
    apply IHind.
    reflexivity.

  (* RConj_e2 *)
  - apply RConj_e2 with A.
    apply IHind.
    reflexivity.

  (* RDisj_i1 *)
  - apply RDisj_i1.
    apply IHind.
    reflexivity.

  (* RDisj_i2 *)
  - apply RDisj_i2.
    apply IHind.
    reflexivity.

  (* RDisj_e *)
  - apply RDisj_e with A B.
    + apply IHind1.
      reflexivity.
    + rewrite app_comm_cons.
      apply IHind2.
      reflexivity.
    + rewrite app_comm_cons.
      apply IHind3.
      reflexivity.

  (* RForAll_i *)
  - apply RForAll_i.
    rewrite <- context_lift_app; simpl.
    apply IHind.
    rewrite context_lift_app.
    reflexivity.

  (* RForAll_e *)
  - apply RForAll_e.
    apply IHind.
    reflexivity.

  (* RExists_i *)
  - apply RExists_i with phi.
    apply IHind.
    reflexivity.

  (* RExists_e *)
  - apply RExists_e with phi.
    + apply IHind1.
      reflexivity.
    + rewrite <- context_lift_app; simpl.
      rewrite app_comm_cons.
      apply IHind2; simpl.
      rewrite context_lift_app.
      reflexivity.
Defined.

(** Γ, Γ' ⊢ φ ⇒ Γ, ψ, Γ' ⊢ φ *)
Lemma derivable_weak (gamma gamma': list formula) (phi phi': formula):
  Derivable (gamma ++ gamma') phi -> Derivable (gamma ++ phi' :: gamma') phi.
Proof.
  intros.
  apply (derivable_weak' (gamma ++ gamma')).
  - assumption.
  - reflexivity.
Defined.

(** Γ ⊢ φ ⇒ Γ, Γ' ⇒ φ *)
Lemma derivable_weak_gamma (gamma gamma': list formula) (phi: formula):
  Derivable gamma phi -> Derivable (gamma' ++ gamma) phi.
Proof.
  intros; induction gamma'; simpl.
  { assumption. }

  apply (derivable_weak nil); simpl.
  assumption.
Defined.

(** Γ ⊢ φ ⇒ ψ, Γ ⇒ φ *)
Lemma derivable_weak_phi (gamma: list formula) (phi phi': formula):
  Derivable gamma phi -> Derivable (phi' :: gamma) phi.
Proof.
  apply (derivable_weak nil).
Defined.

Lemma derivable_lift (gamma: list formula) (phi: formula):
  Derivable gamma phi ->
    forall (idx: nat), Derivable (context_lift idx 1 gamma) (formula_lift idx 1 phi).
Proof.
  induction 1 as
    [ | | ? ? _ IHind |
      (* RImp *)  ? ? ? _ IHind | ? A B _ IHind1 _ IHind2 |
      (* RConj *) ? ? ? _ IHind1 _ IHind2 | ? A B _ IHind | ? A B _ IHind |
      (* RDisj *) ? ? ? _ IHind | ? ? ? _ IHind | ? A B C _ IHind1 _ IHind2 _ IHind3 |
      (* RForAll *) ? ? _ IHind | ? ? ? _ IHind |
      (* RExists *) ? ? phi _ IHind | ? phi ? _ IHind1 _ IHind2 ];
    simpl in *; intros idx'.

  (* RAxiom *)
  - rewrite <- formula_lift_nth.
    apply RAxiom.

  (* RTop_i *)
  - apply RTop_i.

  (* RBot_e *)
  - apply RBot_e.
    apply IHind.

  (* RImp_i *)
  - apply RImp_i.
    apply IHind.

  (* RImp_e *)
  - apply RImp_e with (formula_lift idx' 1 A).
    + apply IHind1.
    + apply IHind2.

  (* RConj_i *)
  - apply RConj_i.
    + apply IHind1.
    + apply IHind2.

  (* RConj_e1 *)
  - apply RConj_e1 with (formula_lift idx' 1 B).
    apply IHind.

  (* RConj_e2 *)
  - apply RConj_e2 with (formula_lift idx' 1 A).
    apply IHind.

  (* RDisj_i1 *)
  - apply RDisj_i1.
    apply IHind.

  (* RDisj_i2 *)
  - apply RDisj_i2.
    apply IHind.

  (* RDisj_e *)
  - apply RDisj_e with (formula_lift idx' 1 A) (formula_lift idx' 1 B).
    + apply IHind1.
    + apply IHind2.
    + apply IHind3.

  (* RForAll_i *)
  - apply RForAll_i.
    rewrite <- (PeanoNat.Nat.add_0_l idx').
    rewrite <- context_lift_S_lift_n; simpl.
    apply IHind.

  (* RForAll_e *)
  - rewrite <- (PeanoNat.Nat.add_0_l idx').
    rewrite <- formula_subst_lift_lift.
    apply RForAll_e.
    apply IHind.

  (* RExists_i *)
  - apply RExists_i with (term_lift idx' 1 phi).
    rewrite (formula_subst_lift_lift _ 0 idx').
    apply IHind.

  (* RExists_e *)
  - apply RExists_e with (formula_lift (S idx') 1 phi).
    + apply IHind1.
    + rewrite <- (PeanoNat.Nat.add_0_l idx').
      rewrite <- context_lift_S_lift_n.
      rewrite <- formula_lift_S_lift_n; simpl.
      apply IHind2.
Defined.

(** (Γ ⊢ φ) ∧ (Γ = Γ', ψ, Γ'') ∧ (Γ'' ⊢ ψ) ⇒ Γ', Γ'' ⊢ φ *)
Lemma derivable_subst' (gamma: list formula) (phi: formula):
  Derivable gamma phi ->
    forall (phi': formula) (gamma' gamma'': list formula),
      gamma = gamma' ++ (phi' :: gamma'') ->
      Derivable gamma'' phi' ->
      Derivable (gamma' ++ gamma'') phi.
Proof.
  induction 1 as
    [ | | ? ? _ IHind |
      (* RImp *)  ? ? ? _ IHind | ? A B _ IHind1 _ IHind2 |
      (* RConj *) ? ? ? _ IHind1 _ IHind2 | ? A B _ IHind | ? A B _ IHind |
      (* RDisj *) ? ? ? _ IHind | ? ? ? _ IHind | ? A B C _ IHind1 _ IHind2 _ IHind3 |
      (* RForAll *) ? ? _ IHind | ? ? ? _ IHind |
      (* RExists *) ? ? phi _ IHind | ? phi ? _ IHind1 _ IHind2 ];
    simpl in *; intros phi'' gamma' gamma'' -> Hphi''.

  (* RAxiom *)
  - destruct (PeanoNat.Nat.eqb_spec idx (length gamma')); subst.
    { rewrite nth_middle.
      apply derivable_weak_gamma.
      apply Hphi''. }

    destruct (PeanoNat.Nat.leb_spec0 (S idx) (length gamma')).
    { rewrite app_nth1; [| lia ].
      rewrite <- (app_nth1 _ gamma''); [| lia ].
      apply RAxiom. }

    replace (nth _ _  _) with (nth (idx - 1) (gamma' ++ gamma'') FTop).
    { apply RAxiom. }

    rewrite !app_nth2; [| lia.. ].
    replace (_ :: _) with ((phi'' :: nil) ++ gamma''); [| reflexivity ].
    rewrite !app_nth2; simpl; [| lia ].
    f_equal.
    lia.

  (* RTop_i *)
  - apply RTop_i.

  (* RBot_e *)
  - apply RBot_e.
    apply (IHind phi''); [ reflexivity |].
    apply Hphi''.

  (* RImp_i *)
  - apply RImp_i.
    apply (IHind phi'' (phi :: gamma')); simpl; [ reflexivity |].
    apply Hphi''.

  (* RImp_e *)
  - apply RImp_e with A.
    + apply (IHind1 phi''); [ reflexivity |].
      apply Hphi''.

    + apply (IHind2 phi''); [ reflexivity |].
      apply Hphi''.

  (* RConj_i *)
  - apply RConj_i.
    + apply (IHind1 phi''); [ reflexivity |].
      apply Hphi''.

    + apply (IHind2 phi''); [ reflexivity |].
      apply Hphi''.

  (* RConj_e1 *)
  - apply RConj_e1 with B.
    apply (IHind phi''); [ reflexivity |].
    apply Hphi''.

  (* RConj_e2 *)
  - apply RConj_e2 with A.
    apply (IHind phi''); [ reflexivity |].
    apply Hphi''.

  (* RDisj_i1 *)
  - apply RDisj_i1.
    apply (IHind phi''); [ reflexivity |].
    apply Hphi''.

  (* RDisj_i2 *)
  - apply RDisj_i2.
    apply (IHind phi''); [ reflexivity |].
    apply Hphi''.

  (* RDisj_e *)
  - apply RDisj_e with A B.
    + apply (IHind1 phi''); [ reflexivity |].
      apply Hphi''.

    + apply (IHind2 phi'' (A :: gamma')); [ reflexivity |].
      apply Hphi''.

    + apply (IHind3 phi'' (B :: gamma')); [ reflexivity |].
      apply Hphi''.

  (* RForAll_i *)
  - apply RForAll_i.
    rewrite <- context_lift_app.

    apply (IHind (formula_lift 0 1 phi'')).
    { rewrite <- context_lift_app; simpl.
      reflexivity. }

    apply derivable_lift.
    apply Hphi''.

  (* RForAll_e *)
  - apply RForAll_e.
    apply IHind with phi''; [ reflexivity |].
    apply Hphi''.

  (* RExists_i *)
  - apply RExists_i with phi.
    apply IHind with phi''; [ reflexivity |].
    apply Hphi''.

  (* RExists_e *)
  - apply RExists_e with phi.
    { apply IHind1 with phi''; [ reflexivity |].
      apply Hphi''. }

    rewrite <- context_lift_app.
    apply (IHind2 (formula_lift 0 1 phi'') (phi :: context_lift 0 1 gamma')); simpl.
    { rewrite <- context_lift_app; simpl.
      reflexivity. }

    apply derivable_lift.
    apply Hphi''.
Defined.

(** (Γ, ψ, Γ' ⊢ φ) ∧ (Γ ⊢ ψ) ⇒ Γ, Γ' ⊢ φ *)
Lemma derivable_subst (gamma gamma': list formula) (phi phi': formula):
  Derivable (gamma' ++ phi' :: gamma) phi ->
    Derivable gamma phi' -> Derivable (gamma' ++ gamma) phi.
Proof.
  intros H1 H2.
  eapply (derivable_subst' _ phi H1 phi'); [ reflexivity |].
  apply H2.
Defined.
