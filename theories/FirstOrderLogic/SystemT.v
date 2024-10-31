Require Import Autosubst.Autosubst.
Require Import List.
Require Import Relations.Relations.
From Coq Require Import Setoid.

(* The types of system T *)
Inductive type : Type :=
| Nat : type
| Arr : type -> type -> type.

Notation "A ~> B" := (Arr A B) (at level 70, right associativity).

(* The syntax of the system T. *)
Inductive term : Type :=
| Var : var -> term
| Lam : {bind term} -> term
| App : term -> term -> term
| Zero : term
| Succ : term -> term
| Rec : type -> term -> term -> term -> term.

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Defined.

Reserved Notation "Gamma |- t : A" (at level 70, t at next level).

Inductive typing : (var -> type) -> type -> term -> Prop :=
| TVar : forall (Gamma : var -> type) (T : type) (n : var),
  Gamma n = T -> Gamma |- Var n : T
| TLam : forall (Gamma : var -> type) (A B : type) (t : term),
  A .: Gamma |- t : B -> Gamma |- Lam t : (A ~> B)
| TApp : forall (Gamma : var -> type) (A B : type) (t u : term),
  Gamma |- t : (A ~> B) -> Gamma |- u : A ->
  Gamma |- App t u : B
| TZero : forall (Gamma : var -> type), Gamma |- Zero : Nat
| TSucc : forall (Gamma : var -> type) (t : term),
  Gamma |- t : Nat -> Gamma |- Succ t : Nat
| TRec : forall (Gamma : var -> type) (A : type) (t u v : term),
  Gamma |- t : Nat -> Gamma |- u : A -> Gamma |- v : (Nat ~> A ~> A) ->
  Gamma |- Rec A t u v : A
where "Gamma |- t : A" := (typing Gamma A t).

Lemma ty_renaming :
  forall (Gamma : var -> type) (A : type) (t : term),
  Gamma |- t : A ->
  forall (Delta : var -> type) (Xi : var -> var),
  Gamma = Xi >>> Delta ->
  Delta |- t.[ren Xi] : A.
Proof.
  intros Gamma A t H.
  induction H as [ Gamma T n Heq | Gamma A A' t Ht IHt |
    Gamma A A' t u Ht IHt Hu IHu | Gamma | Gamma t Ht IHt
    | Gamma A t u v Ht IHt Hu IHu Hv IHv ];
    intros Delta Xi H; asimpl; subst;
    asimpl; econstructor;
    try solve [ now reflexivity | now (apply IHt; asimpl) |
    now (apply IHu; asimpl) | now (apply IHv; asimpl) ].
Qed.

Theorem ty_weakening : forall (Gamma : var -> type) (A : type)
  (t : term), Gamma |- t : A ->
  forall (Delta : var -> type) (sigma : var -> term),
  (forall (v : var), Delta |- sigma v : (Gamma v)) ->
  Delta |- t.[sigma] : A.
Proof.
  intros Gamma A t H.
  induction H as [ Gamma T n Heq | Gamma A B t Ht IHt |
    Gamma A B t u Ht IHt Hu IHu | Gamma | Gamma t Ht IHt
    | Gamma A t u v Ht IHt Hu IHu Hv IHv ];
    intros Delta sigma Hvar;
    asimpl; subst; [ idtac | econstructor.. ];
    try solve [now apply IHt | now apply IHu | now apply IHv].
  - apply Hvar.
  - apply IHt with (Delta := A .: Delta).
    intros [|v]; asimpl.
    + now constructor.
    + apply ty_renaming with (Gamma := Delta).
      * apply Hvar.
      * now asimpl.
Qed.

Inductive red : term -> term -> Prop :=
| RBetaLam : forall (s t u : term), s.[t/] = u ->
  red (App (Lam s) t) u
| RBetaRecZ : forall (A : type) (u v : term),
  red (Rec A Zero u v) u
| RBetaRecS : forall (A : type) (t u v : term),
  red (Rec A (Succ t) u v) (App (App v t) (Rec A t u v))
| RAppL : forall (s s' t : term),
  red s s' -> red (App s t) (App s' t)
| RAppR : forall (s t t' : term),
  red t t' -> red (App s t) (App s t')
| RLam : forall (t t' : term),
  red t t' -> red (Lam t) (Lam t')
| RSucc : forall (t t' : term),
  red t t' -> red (Succ t) (Succ t')
| RRecN : forall (A : type) (t t' u v : term),
  red t t' -> red (Rec A t u v) (Rec A t' u v)
| RRecZ : forall (A : type) (t u u' v : term),
  red u u' -> red (Rec A t u v) (Rec A t u' v)
| RRecS : forall (A : type) (t u v v' : term),
  red v v' -> red (Rec A t u v) (Rec A t u v').

Theorem ty_preservation :
  forall (Gamma : var -> type) (A : type) (t t' : term),
  Gamma |- t : A -> red t t' -> Gamma |- t' : A.
Proof.
  intros Gamma A t t' Htyp Hred.
  generalize dependent A.
  generalize dependent Gamma.
  induction Hred as [ s t u Heq | B u v | B t u v |
  s s' t H IH | s t t' H IH | t t' H IH | t t' H IH |
  B t t' u v H IH | B t u u' v H IH | B t u v v' H IH];
  intros Gamma A Htyp;
  inversion Htyp; subst;
  try (econstructor;
    solve [eapply IH; eassumption | eassumption]).
  - inversion H3; subst.
    apply ty_weakening with (Gamma := A0 .: Gamma).
    + assumption.
    + intros [|v]; asimpl.
      * assumption.
      * now constructor.
  - assumption.
  - inversion H4; subst.
    econstructor.
    + econstructor; eassumption.
    + econstructor; eassumption.
Qed.

Inductive par_red : term -> term -> Prop :=
| PRReflVar : forall (v : var), par_red (Var v) (Var v)
| PRReflZero : par_red Zero Zero
| PRBetaLam : forall (s s' t t' u : term),
  par_red s s' -> par_red t t' ->
  s'.[t'/] = u -> par_red (App (Lam s) t) u
| PRBetaRecZ : forall (A : type) (u u' v : term),
  par_red u u' -> par_red (Rec A Zero u v) u'
| PRBetaRecS : forall (A : type) (t t' u u' v v' : term),
  par_red t t' -> par_red u u' -> par_red v v' ->
  par_red (Rec A (Succ t) u v) (App (App v' t') (Rec A t' u' v'))
| PRApp : forall (s s' t t' : term),
  par_red s s' -> par_red t t' ->
  par_red (App s t) (App s' t')
| PRLam : forall (t t' : term),
  par_red t t' -> par_red (Lam t) (Lam t')
| PRSucc : forall (t t' : term),
  par_red t t' -> par_red (Succ t) (Succ t')
| PRRec : forall (A : type) (t t' u u' v v' : term),
  par_red t t' -> par_red u u' -> par_red v v' ->
  par_red (Rec A t u v) (Rec A t' u' v').

Notation "R *" := (clos_refl_trans _ R)
  (at level 8, no associativity, format "R *").

#[export] Instance par_red_refl : Reflexive par_red.
Proof.
  unfold Reflexive.
  intros t.
  induction t; constructor; assumption.
Qed.

#[export] Instance red_star_refl : Reflexive red*.
Proof.
  constructor; apply rt_refl.
Qed.

#[export] Instance red_star_trans : Transitive red*.
Proof.
  unfold Transitive.
  intros.
  eapply rt_trans; eassumption.
Qed.

Add Parametric Relation : term red* as red_rel.

Add Parametric Morphism : Lam
  with signature red* ==> red*
  as Lam_morph.
Proof.
  intros t t' Ht.
  induction Ht.
  - constructor. now constructor.
  - reflexivity.
  - etransitivity; eassumption.
Qed.

Add Parametric Morphism : App
  with signature red* ==> red* ==> red*
  as App_morph.
Proof.
  assert (Ht' : forall t t' s, (red* t t') -> red* (App t s) (App t' s)). {
    intros t t' s Ht.
    induction Ht.
    - constructor. now constructor.
    - reflexivity.
    - etransitivity; eassumption.
  }
  assert (Hs' : forall t s s', (red* s s') -> red* (App t s) (App t s')). {
    intros t s s' Hs.
    induction Hs.
    - constructor. now constructor.
    - reflexivity.
    - etransitivity; eassumption.
  }
  intros t t' Ht s s' Hs.
  rewrite Ht' by eassumption.
  rewrite Hs' by eassumption.
  reflexivity.
Qed.

Add Parametric Morphism : Succ
  with signature red* ==> red*
  as Succ_morph.
Proof.
  intros t t' Ht.
  induction Ht.
  - constructor. now constructor.
  - reflexivity.
  - etransitivity; eassumption.
Qed.

Add Parametric Morphism (A : type) : (Rec A)
  with signature red* ==> red* ==> red* ==> red*
  as Rec_morph.
Proof.
  assert (Ht' : forall t t' u v, (red* t t') -> red* (Rec A t u v) (Rec A t' u v)). {
    intros t t' u v Ht.
    induction Ht.
    - constructor. now constructor.
    - reflexivity.
    - etransitivity; eassumption.
  }
  assert (Hu' : forall t u u' v, (red* u u') -> red* (Rec A t u v) (Rec A t u' v)). {
    intros t u u' v Hu.
    induction Hu.
    - constructor. now constructor.
    - reflexivity.
    - etransitivity; eassumption.
  }
  assert (Hv' : forall t u v v', (red* v v') -> red* (Rec A t u v) (Rec A t u v')). {
    intros t u v v' Hv.
    induction Hv.
    - constructor. now constructor.
    - reflexivity.
    - etransitivity; eassumption.
  }
  intros t t' Ht u u' Hu  v v' Hv.
  rewrite Ht' by eassumption.
  rewrite Hu' by eassumption.
  rewrite Hv' by eassumption.
  reflexivity.
Qed.

Lemma red_to_par_red : forall (s t : term),
  red s t -> par_red s t.
Proof.
  intros s t H.
  induction H as [ s t u Heq | B u v | B t u v |
  s s' t H IH | s t t' H IH | t t' H IH | t t' H IH |
  B t t' u v H IH | B t u u' v H IH | B t u v v' H IH].
  - eapply PRBetaLam; [ reflexivity.. | assumption ].
  - eapply PRBetaRecZ; reflexivity.
  - eapply PRBetaRecS; reflexivity.
  - eapply PRApp; [apply IH | reflexivity].
  - eapply PRApp; [reflexivity | apply IH].
  - eapply PRLam; apply IH.
  - eapply PRSucc; apply IH.
  - eapply PRRec; [apply IH | reflexivity | reflexivity].
  - eapply PRRec; [ reflexivity | apply IH | reflexivity].
  - eapply PRRec; [reflexivity | reflexivity | apply IH].
Qed.

Lemma par_red_to_red_star : forall (s t : term),
  par_red s t -> red* s t.
Proof.
  intros s t H.
  induction H as [ v | | s s' t t' u Hs IHs Ht IHt Heq |
  A u u' v Hu IHu | A t t' u u' v v' Ht IHt Hu IHu Hv IHv |
  s s' t t' Hs IHs Ht IHt | t t' Ht IHt | t t' Ht IHt |
  A t t' u u' v v' Ht IHt Hu IHu Hv IHv ].
  - reflexivity.
  - reflexivity.
  - rewrite IHs.
    rewrite IHt.
    constructor.
    now constructor.
  - etransitivity.
    + apply rt_step.
      constructor.
    + assumption.
  - etransitivity.
    + apply rt_step.
      constructor.
    + now rewrite IHt, IHu, IHv.
  - now rewrite IHs, IHt.
  - now rewrite IHt.
  - now rewrite IHt.
  - now rewrite IHt, IHu, IHv.
Qed.

Lemma red_par_red_clos :
  forall (s t : term), red* s t <-> par_red* s t.
Proof.
  intros s t.
  split; intros H.
  + induction H as [ t t' H | t | t t' t'' Ht IHt Ht' IHt' ].
    - apply rt_step.
      now apply red_to_par_red.
    - apply rt_refl.
    - eapply rt_trans; eassumption.
  + induction H as [ t t' H | t | t t' t'' Ht IHt Ht' IHt' ].
    - now apply par_red_to_red_star.
    - reflexivity.
    - etransitivity; eassumption.
Qed.

Lemma par_red_renaming : forall (t t' : term), par_red t t' ->
  forall (Xi : var -> var),
  par_red t.[ren Xi] t'.[ren Xi].
Proof.
  intros t t' H.
  induction H as [ v | | s s' t t' u Hs IHs Ht IHt Heq |
  A u u' v Hu IHu | A t t' u u' v v' Ht IHt Hu IHu Hv IHv |
  s s' t t' Hs IHs Ht IHt | t t' Ht IHt | t t' Ht IHt |
  A t t' u u' v v' Ht IHt Hu IHu Hv IHv ];
  intros Xi; asimpl; subst;
  asimpl; try (econstructor; solve [ now reflexivity | now (apply IHt; asimpl) |
    now (apply IHu; asimpl) | now (apply IHv; asimpl) |
    (now apply IHs; asimpl) ]).
  econstructor.
  - now apply IHs.
  - now apply IHt.
  - asimpl.
    reflexivity.
Qed.

Lemma par_red_subst : forall (t t' : term), par_red t t' ->
  forall (sigma sigma' : var -> term),
  (forall (v : var), par_red (sigma v) (sigma' v)) ->
  par_red t.[sigma] t'.[sigma'].
Proof.
  intros t t' Ht.
  assert (H' : forall (sigma sigma' : var -> term),
    (forall (v : var), par_red (sigma v) (sigma' v)) ->
    forall v : var, par_red (up sigma v) (up sigma' v)).
  {
    intros sigma sigma' H [|v]; asimpl.
    + reflexivity.
    + apply par_red_renaming.
      apply H.
  }
  induction Ht as [ v | | s s' t t' u Hs IHs Ht IHt Heq |
  A u u' v Hu IHu | A t t' u u' v v' Ht IHt Hu IHu Hv IHv |
  s s' t t' Hs IHs Ht IHt | t t' Ht IHt | t t' Ht IHt |
  A t t' u u' v v' Ht IHt Hu IHu Hv IHv ];
  intros sigma sigma' H; asimpl; subst; asimpl;
  try (econstructor; solve [ now reflexivity |
    now (apply IHu; asimpl) | now (apply IHv; asimpl)
  | now (apply IHt; asimpl) | now (apply IHs; asimpl) ]).
  - apply H.
  - econstructor.
    + apply IHs.
      now apply H'.
    + now apply IHt.
    + asimpl.
      reflexivity.
  - constructor.
    apply IHt.
    now apply H'.
Qed.

Fixpoint max_par_reduct (t : term) : term := match t with
| Var v => Var v
| Zero => Zero
| App (Lam t) u => (max_par_reduct t).[(max_par_reduct u)/]
| App t u => App (max_par_reduct t) (max_par_reduct u)
| Lam t => Lam (max_par_reduct t)
| Succ t => Succ (max_par_reduct t)
| Rec A Zero u v => max_par_reduct u
| Rec A (Succ t) u v => App (App (max_par_reduct v) (max_par_reduct t)) (Rec A (max_par_reduct t) (max_par_reduct u) (max_par_reduct v)) 
| Rec A t u v => Rec A (max_par_reduct t) (max_par_reduct u) (max_par_reduct v)
end.

Lemma Lam_match : forall (s u : term) (f : term -> term),
let m := match s with
| Lam s' => f s'
| _ => u
end in (exists s', s = Lam s' /\ m = f s') \/
  (m = u /\ ~exists s', s = Lam s').
Proof.
  intros s u f m.
  destruct s as [ | s' | | | | ].
  2: eauto.
  all: right; split; eauto; intros [? H]; inversion H.
Qed.

Lemma Rec_match : forall (s t u : term) (f : term -> term),
let m := match s with
| Zero => t
| Succ s' => f s'
| _ => u
end in (s = Zero /\ m = t) \/
(exists s', s = Succ s' /\ m = f s') \/
  (m = u /\ ~s = Zero /\ ~exists s', s = Succ s').
Proof.
  intros s t u f m.
  destruct s as [ | | | | s' | ].
  4,5: eauto.
  all: right; right; split; try eauto;
  split; [ intros H | intros [? H]]; inversion H.
Qed.

Lemma max_par_red : forall (t t' : term),
  par_red t t' -> par_red t' (max_par_reduct t).
Proof.
  intros t t' Ht.
  induction Ht as [ v | | s s' t t' u Hs IHs Ht IHt Heq |
  A u u' v Hu IHu | A t t' u u' v v' Ht IHt Hu IHu Hv IHv |
  s s' t t' Hs IHs Ht IHt | t t' Ht IHt | t t' Ht IHt |
  A t t' u u' v v' Ht IHt Hu IHu Hv IHv ]; asimpl.
  - reflexivity.
  - reflexivity.
  - subst.
    apply par_red_subst.
    + assumption.
    + intros [| v]; asimpl; [ assumption | reflexivity ].
  - assumption.
  - constructor; [ constructor | constructor ]; assumption.
  - set (f :=  fun s' => (max_par_reduct s').[max_par_reduct t/]).
    destruct (Lam_match s (App (max_par_reduct s) (max_par_reduct t)) f)
      as [(t0 & H1 & H2) | (H1 & H2)]; subst.
    + inversion Hs; subst.
      inversion IHs; subst.
      econstructor; eassumption.
    + unfold f in *.
      rewrite H1.
      constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - set (f := fun t0 =>  App (App (max_par_reduct v) (max_par_reduct t0))
      (Rec A (max_par_reduct t0) (max_par_reduct u) (max_par_reduct v))).
    destruct (Rec_match t (max_par_reduct u)
      (Rec A (max_par_reduct t) (max_par_reduct u) (max_par_reduct v)) f)
    as [ (H1 & H2) | [(t0 & H1 & H2) | (H1 & H2 & H3)]]; subst.
    + inversion Ht; subst.
      constructor; assumption.
    + inversion Ht; subst.
      inversion IHt; subst.
      constructor; assumption.
    + unfold f in *.
      rewrite H1.
      constructor; assumption.
Qed.

Definition local_confluence (P : term -> term -> Prop) : Prop :=
  forall (t u v : term), P t u -> P t v ->
  exists (w : term), P u w /\ P v w.

Definition ChurchRosser (P : term -> term -> Prop) :=
  local_confluence (clos_refl_trans _ P).

Lemma local_confluence_par_red : local_confluence par_red.
Proof.
  intros t u v Hu Hv.
  exists (max_par_reduct t).
  split; apply max_par_red; assumption.
Qed.

Lemma CR_par_red_left : forall (t u v : term),
  par_red t u -> par_red* t v ->
  exists (w : term), par_red* u w /\ par_red v w.
Proof.
  intros t u v Hu Hv.
  generalize dependent u.
  induction Hv as [ t v Hv | t | t v v' Hv IHv Hv' IHv'];
  intros u Hu.
  - destruct (local_confluence_par_red t u v Hu Hv) as (w & H1 & H2).
    exists w.
    split; [ constructor | idtac ]; assumption.
  - exists u.
    split; [ constructor | idtac ]; assumption.
  - specialize (IHv _ Hu) as (u' & H1 & H2).
    specialize (IHv' _ H2) as (w & H3 & H4).
    exists w.
    split; [ eapply rt_trans | idtac ]; eassumption.
Qed.

Lemma CR_par_red : ChurchRosser par_red.
Proof.
  intros t u v Hu Hv.
  generalize dependent v.
  induction Hu as [t u Hu | t | t u u' Hu IHu Hu' IHu'];
  intros v Hv.
  - destruct (CR_par_red_left t u v Hu Hv) as (w & H1 & H2).
    exists w.
    split; auto.
    now apply rt_step.
  - exists v.
    split; auto.
    now apply rt_refl.
  - destruct (IHu _ Hv) as (w & H1 & H2).
    destruct (IHu' _ H1) as (w' & H3 & H4).
    exists w'.
    split; auto.
    eapply rt_trans; eassumption.
Qed.

Theorem CR_red : ChurchRosser red.
Proof.
  intros t u v Hu Hv.
  rewrite red_par_red_clos in *.
  specialize (CR_par_red t u v Hu Hv) as (w & H1 & H2).
  exists w.
  rewrite <- red_par_red_clos in *.
  auto.
Qed.
