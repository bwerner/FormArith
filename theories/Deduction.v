From FormArith Require Import Definitions Lifts.

Require Import Lia.


Inductive Derivable: list formula -> formula -> Type :=
  | RAxiom (gamma: list formula) (idx: nat):
      Derivable gamma (nth idx gamma FTop)

  | RTop_i (gamma: list formula):
      Derivable gamma FTop

  | RBot_e (gamma: list formula) (phi: formula):
      Derivable gamma FBot -> Derivable gamma phi

  | RImp_i (gamma: list formula) (phi phi': formula):
      Derivable (phi :: gamma) phi' -> Derivable gamma (FImp phi phi')

  | RImp_e (gamma: list formula) (phi phi': formula):
      Derivable gamma phi -> Derivable gamma (FImp phi phi') -> Derivable gamma phi'

  | RConj_i (gamma: list formula) (phi phi': formula):
      Derivable gamma phi -> Derivable gamma phi' -> Derivable gamma (FConj phi phi')

  | RConj_e1 (gamma: list formula) (phi phi': formula):
      Derivable gamma (FConj phi phi') -> Derivable gamma phi

  | RConj_e2 (gamma: list formula) (phi phi': formula):
      Derivable gamma (FConj phi phi') -> Derivable gamma phi'

  | RDisj_i1 (gamma: list formula) (phi phi': formula):
      Derivable gamma phi -> Derivable gamma (FDisj phi phi')

  | RDisj_i2 (gamma: list formula) (phi phi': formula):
      Derivable gamma phi' -> Derivable gamma (FDisj phi phi')

  | RDisj_e (gamma: list formula) (phi phi' phi'': formula):
      Derivable gamma (FDisj phi phi') ->
      Derivable (phi :: gamma) phi'' -> Derivable (phi' :: gamma) phi'' ->
      Derivable gamma phi''

  | RForAll_i (gamma: list formula) (phi: formula):
      Derivable (context_lift 0 1 gamma) phi -> Derivable gamma (FForAll phi)

  | RForAll_e (gamma: list formula) (phi: formula) (t: term):
      Derivable gamma (FForAll phi) -> Derivable gamma (formula_subst 0 t phi)

  | RExists_i (gamma: list formula) (phi: formula) (t: term):
      Derivable gamma (formula_subst 0 t phi) -> Derivable gamma (FExists phi)

  | RExists_e (gamma: list formula) (phi phi': formula):
      Derivable gamma (FExists phi) ->
      Derivable (phi :: context_lift 0 1 gamma) (formula_lift 0 1 phi') ->
      Derivable gamma phi'.


Lemma derivable_correctness (fcts: nat -> list nat -> nat) (preds: nat -> list nat -> Prop)
    (gamma: list formula) (phi: formula):
  Derivable gamma phi ->
    forall (sigma: list nat),
      (forall (idx: nat), formula_eval fcts preds sigma (nth idx gamma FTop)) ->
        formula_eval fcts preds sigma phi.
Proof.
  induction 1 as
    [ | | ? ? _ IHind |
      (* RImp *)  ? ? ? _ IHind | ? ? ? _ IHind1 _ IHind2 |
      (* RConj *) ? ? ? _ IHind1 _ IHind2 | ? ? ? _ IHind | ? ? ? _ IHind |
      (* RDisj *) ? ? ? _ IHind | ? ? ? _ IHind | ? ? ? ? _ IHind1 _ IHind2 _ IHind3 |
      (* RForAll *) ? ? _ IHind | ? ? t _ IHind |
      (* RExists *) ? ? t _ IHind | ? ? ? _ IHind1 _ IHind2 ];
    simpl in *; intros sigma IHtree; intros.

  (* RAxiom *)
  - apply IHtree.

  (* RTop_i *)
  - exact I.

  (* RTop_e *)
  - exfalso.
    apply (IHind sigma).
    apply IHtree.

  (* RImp_i *)
  - apply (IHind sigma).
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
  - destruct (IHind1 sigma IHtree).
    + apply IHind2.
      intros [|]; [ assumption | apply IHtree ].
    + apply IHind3.
      intros [|]; [ assumption | apply IHtree ].

  (* RForAll_i *)
  - apply IHind; intros n.
    rewrite formula_lift_nth.
    apply formula_eval_S with (sigma := nil).
    apply IHtree.

  (* RForAll_e *)
  - replace t with (term_lift 0 0 t).
    2: { apply term_lift_0. }

    apply formula_eval_subst_lift with (sigma := nil).
    apply IHind.
    apply IHtree.

  (* RExists_i *)
  - exists (term_eval fcts sigma t).
    apply formula_eval_subst_lift with (sigma := nil).
    rewrite term_lift_0.
    apply IHind.
    apply IHtree.

  (* RExists_e *)
  - destruct (IHind1 sigma IHtree) as [ n ? ].
    apply formula_eval_S with (sigma := nil) (idx := n).
    apply IHind2.

    intros [|]; [ assumption |].
    rewrite formula_lift_nth.
    apply formula_eval_S with (sigma := nil).
    apply IHtree.
Qed.

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
      (* RExists *) ? ? t _ IHind | ? t ? _ IHind1 _ IHind2 ];
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

  (* RTop_e *)
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
  - apply RExists_i with t.
    apply IHind.
    reflexivity.

  (* RExists_e *)
  - apply RExists_e with t.
    + apply IHind1.
      reflexivity.
    + rewrite <- context_lift_app; simpl.
      rewrite app_comm_cons.
      apply IHind2; simpl.
      rewrite context_lift_app.
      reflexivity.
Defined.

Lemma derivable_weak (gamma gamma': list formula) (phi phi': formula):
  Derivable (gamma ++ gamma') phi -> Derivable (gamma ++ phi' :: gamma') phi.
Proof.
  intros.
  apply (derivable_weak' (gamma ++ gamma')).
  - assumption.
  - reflexivity.
Defined.

Lemma derivable_weak_gamma (gamma gamma': list formula) (phi: formula):
  Derivable gamma phi -> Derivable (gamma' ++ gamma) phi.
Proof.
  intros; induction gamma'; simpl.
  { assumption. }

  apply (derivable_weak nil); simpl.
  assumption.
Defined.

Lemma derivable_weak_phi (gamma: list formula) (phi phi': formula):
  Derivable gamma phi -> Derivable (phi' :: gamma) phi.
Proof.
  apply (derivable_weak nil).
Defined.
