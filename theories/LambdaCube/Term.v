From Coq Require Import Utf8.
From Coq Require Import Arith Lia.
From FormArith Require Import Base.

Inductive sort : Type :=
| Star : sort
| Box : sort.

(* Terms of the Lambda Cube with n free variables.
   Variables are represented as De Bruijn levels.
   The free variable most recently introduced in
   a term with (n + 1) free variables has value n
 *)
Inductive term (n : nat) : Type :=
| Var : {k | k < n} → term n
| Pi : term n → term (S n) → term n
| Abs : term n → term (S n) → term n
| App : term n → term n → term n
| Srt : sort → term n.

Arguments Var {n}.
Arguments Pi {n}.
Arguments Abs {n}.
Arguments App {n}.
Arguments Srt {n}.

(* Execution contexts of the Lambda Cube with n free variables. *)
Inductive ctx (k : nat) : nat → Type :=
| Hole : ctx k k
| PiL {n} : ctx k n → term (S n) → ctx k n
| AbsL {n} : ctx k n → term (S n) → ctx k n
| AppL {n} : ctx k n → term n → ctx k n
| PiR {n} : term n → ctx k (S n) → ctx k n
| AbsR {n} : term n → ctx k (S n)→ ctx k n
| AppR {n} : term n → ctx k n → ctx k n.

Arguments Hole {k}.
Arguments PiL {k n}.
Arguments AbsL {k n}.
Arguments AppL {k n}.
Arguments PiR {k n}.
Arguments AbsR {k n}.
Arguments AppR {k n}.

Lemma sig_lt_ext {k : nat} (p q : {i | i < k}) :
  proj1_sig p = proj1_sig q → p = q.
Proof.
  destruct p, q.
  simpl.
  intros ->.
  f_equal.
  apply le_unique.
Qed.

Lemma ctx_le n k : ctx k n -> n <= k.
Proof.
  induction 1; lia.
Qed.

Lemma not_ctx_S_0 {n} : ctx 0 (S n) -> False.
Proof.
  intro K. apply ctx_le in K. lia.
Qed.

(* Basic weakening renaming *)
Definition weaken {k : nat} (i : {i | i < k}) : {i | i < S k} :=
  exist _ (proj1_sig i) (Nat.lt_lt_succ_r _ _ (proj2_sig i)).

(* Lifting of variable renamings *)
Definition lift
  {k n : nat} (σ : {i | i < k} → {i | i < n})
  (i : {i | i < S k}) : {i | i < S n}
  :=
  match lt_dec (proj1_sig i) k with
  | left Hi => weaken (σ (exist _ (proj1_sig i) Hi))
  | right _ => exist _ n (Nat.lt_succ_diag_r n)
  end.

Lemma lift_weaken
  {k n : nat}
  (σ : {i | i < k} → {i | i < n})
  (i :  {i | i < k}) :
  lift σ (weaken i) = weaken (σ i).
Proof.
  unfold lift.
  destruct (lt_dec _ _) as [|Hge].
  - do 2 f_equal.
    now apply sig_lt_ext.
  - contradict Hge.
    simpl.
    apply proj2_sig.
Qed.

Lemma lift_ext
  {k n : nat}
  (σ1 σ2: {i | i < k} → {i | i < n}) :
  (∀ i, σ1 i = σ2 i) →
  ∀ (i : {i | i < S k}),
  lift σ1 i = lift σ2 i.
Proof.
  intros σ_eq i.
  unfold lift.
  destruct (lt_dec (proj1_sig i) k).
  - congruence.
  - reflexivity.
Qed.

Lemma lift_comp :
  ∀ {k m n : nat}
  (σ1 : {i | i < k} → {i | i < m})
  (σ2 : {i | i < m} → {i | i < n})
  (i : {i | i < S k}),
  lift σ2 (lift σ1 i) = lift (σ2 ∘ σ1) i.
Proof.
  intros k m n σ1 σ2 i.
  unfold lift.
  destruct (lt_dec (proj1_sig i) k);
    destruct (lt_dec _ _) as [Hlt | Hge]; simpl in *; try lia.
  - do 2 f_equal.
    now apply sig_lt_ext.
  - contradict Hge.
    apply proj2_sig.
  - reflexivity.
Qed.

Lemma lift_lt {k n : nat} (σ : {i | i < k} → {i | i < n}) (i : nat)
  : ∀ Hik HiSk, proj1_sig (lift σ (exist _ i HiSk)) = proj1_sig (σ (exist _ i Hik)).
Proof.
  intros Hik HiSk.
  simpl.
  unfold lift.
  destruct (lt_dec _ _); [|now contradict Hik].
  simpl.
  do 2 f_equal.
  now apply sig_lt_ext.
Qed.
  
Lemma lift_eq {k n : nat} (σ : {i | i < k} → {i | i < n}) 
  : ∀ Hk, proj1_sig (lift σ (exist _ k Hk)) = n.
Proof.
  intros.
  unfold lift.
  destruct (lt_dec _ _); simpl in *; [lia|reflexivity].
Qed.

(* Renaming of free variables in a term *)
Fixpoint ren {k n : nat} (σ : {i | i < k} → {i | i < n}) (t : term k) : term n :=
  match t with
  | Var i => Var (σ i)
  | Pi ty fam => Pi (ren σ ty) (ren (lift σ) fam)
  | Abs ty tm => Abs (ren σ ty) (ren (lift σ) tm)
  | App tm1 tm2 => App (ren σ tm1) (ren σ tm2)
  | Srt s => Srt s
  end.

(* Plug a term in place of the hole in a context *)
Fixpoint fill {k n : nat} (K : ctx k n) (t : term k) : term n :=
  match K in ctx _ n with
  | Hole => t
  | PiL K fam => Pi (fill K t) fam
  | AbsL K tm => Abs (fill K t) tm
  | AppL K tm => App (fill K t) tm
  | PiR ty K => Pi ty (fill K t)
  | AbsR ty K => Abs ty (fill K t)
  | AppR tm K => App tm (fill K t)
  end.

Fixpoint fillK {k n m : nat} (K : ctx n m) (C : ctx k n) : ctx k m :=
  match K in ctx _ m0 return ctx k m0 with
  | Hole => C
  | PiL K fam => PiL (fillK K C) fam
  | AbsL K tm => AbsL (fillK K C) tm
  | AppL K tm => AppL (fillK K C) tm
  | PiR ty K => PiR ty (fillK K C)
  | AbsR ty K => AbsR ty (fillK K C)
  | AppR tm K => AppR tm (fillK K C)
  end.

Lemma ren_ext :
  ∀ {k n : nat}
  (σ1 σ2: {i | i < k} → {i | i < n})
  (t : term k),
  (∀ i, σ1 i = σ2 i) →
  ren σ1 t = ren σ2 t.
Proof.
  fix IH 5.
  intros k n σ1 σ2 t σ_eq.
  destruct t;
    simpl;
    try congruence;
    f_equal;
    try now apply IH.
  all : apply IH, lift_ext, σ_eq.
Qed.

Lemma ren_comp :
  ∀ {k m n : nat}
  (σ1 : {i | i < k} → {i | i < m})
  (σ2 : {i | i < m} → {i | i < n})
  (t : term k),
  ren σ2 (ren σ1 t) = ren (σ2 ∘ σ1) t.
Proof.
  fix IH 6.
  intros k m n σ1 σ2 t.
  destruct t; simpl; try easy.
  1,2 :
    rewrite !IH;
    f_equal;
    apply ren_ext;
    intros i;
    apply lift_comp.
  now rewrite !IH.
Qed.

Lemma fill_fillK {k n m : nat} (K : ctx n m) (K': ctx k n) t :
  fill (fillK K K') t = fill K (fill K' t).
Proof.
  induction K; simpl; try congruence; destruct k; try solve [destruct (not_ctx_S_0 _)]; simpl;
    f_equal; rewrite IHK; f_equal; symmetry; apply ren_fill.
Qed.

(* Lifting of variable substitutions *)
Definition lift_bind {k n : nat} (σ : {i | i < k} → term n) (i : {i | i < S k}) : term (S n) :=
  match lt_dec (proj1_sig i) k with
  | left Hi => ren weaken (σ (exist _ (proj1_sig i) Hi))
  | right _ => Var (exist _ n (Nat.lt_succ_diag_r n))
  end.

Lemma lift_bind_weaken
  {k n : nat}
  (σ : {i | i < k} → term n)
  (i :  {i | i < k}) :
  lift_bind σ (weaken i) = ren weaken (σ i).
Proof.
  unfold lift_bind.
  destruct (lt_dec _ _) as [|Hge].
  - do 2 f_equal.
    now apply sig_lt_ext.
  - contradict Hge.
    simpl.
    apply proj2_sig.
Qed.

Lemma lift_bind_ext
  {k n : nat}
  (σ1 σ2: {i | i < k} → term n) :
  (∀ i, σ1 i = σ2 i) →
  ∀ (i : {i | i < S k}),
  lift_bind σ1 i = lift_bind σ2 i.
Proof.
  intros σ_eq i.
  unfold lift_bind.
  destruct (lt_dec (proj1_sig i) k).
  - congruence.
  - reflexivity.
Qed.

(* Substitution of free variables inside a term *)
Fixpoint bind {k n : nat} (σ : {i | i < k} → term n) (t : term k) : term n
  :=
  match t with
  | Var i => σ i
  | Pi ty fam => Pi (bind σ ty) (bind (lift_bind σ) fam)
  | Abs ty tm => Abs (bind σ ty) (bind (lift_bind σ) tm)
  | App tm1 tm2 => App (bind σ tm1) (bind σ tm2)
  | Srt s => Srt s
  end.

Lemma bind_ext :
  ∀ {k n : nat}
  (σ1 σ2: {i | i < k} → term n)
  (t : term k),
  (∀ i, σ1 i = σ2 i) →
  bind σ1 t = bind σ2 t.
Proof.
  fix IH 5.
  intros k n σ1 σ2 t σ_eq.
  destruct t;
    simpl;
    try congruence;
    f_equal;
    try now apply IH.
  all : apply IH, lift_bind_ext, σ_eq.
Qed.

Lemma bind_id :
  ∀ {n} (σ : {i | i < n} -> term n) (t: term n), (forall k, σ k = Var k) -> bind σ t = t.
  induction t; simpl; auto.
  - intro. f_equal.
    + apply IHt1. assumption.
    + apply IHt2. unfold lift_bind. intro. destruct (lt_dec _ _).
      * rewrite H. simpl. f_equal. apply sig_lt_ext. reflexivity.
      * f_equal. apply sig_lt_ext. simpl. pose proof (proj2_sig k); simpl in *. lia.
  - intro. f_equal.
    + apply IHt1. assumption.
    + apply IHt2. unfold lift_bind. intro. destruct (lt_dec _ _).
      * rewrite H. simpl. f_equal. apply sig_lt_ext. reflexivity.
      * f_equal. apply sig_lt_ext. simpl. pose proof (proj2_sig k); simpl in *. lia.
  - intro. f_equal; auto.
Qed.

Lemma lift_bind_lift :
  ∀ {k m n : nat}
    (σ1 : {i | i < k} → {i | i < m})
    (σ2 : {i | i < m} → term n)
    (i : {i | i < S k}),
  lift_bind σ2 (lift σ1 i) = lift_bind (σ2 ∘ σ1) i.
Proof.
  intros k m n σ1 σ2 i.
  unfold lift at 1, lift_bind at 2.
  destruct (lt_dec _ _).
  - unfold lift_bind at 1.
    destruct (lt_dec _ _) as [|Hge].
    + do 2 f_equal.
      now apply sig_lt_ext.
    + contradict Hge.
      simpl.
      apply proj2_sig.
  - unfold lift_bind at 1.
    destruct (lt_dec _ _) as [Hlt|].
    + simpl in Hlt. lia.
    + reflexivity.
Qed.

Lemma bind_ren :
  ∀ {k m n : nat}
    (σ1 : {i | i < k} → {i | i < m})
    (σ2 : {i | i < m} → term n)
    (t : term k),
  bind σ2 (ren σ1 t) = bind (σ2 ∘ σ1) t.
Proof.
  fix IH 6.
  intros k m n σ1 σ2 t.
  destruct t; simpl; try reflexivity.
  1,2:
    rewrite IH;
    f_equal;
    rewrite IH;
    apply bind_ext;
    intros i;
    apply lift_bind_lift.
  now rewrite !IH.
Qed.

Lemma lift_bind_ren :
  ∀ {k m n : nat}
    (σ1 : {i | i < k} → term m)
    (σ2 : {i | i < m} → {i | i < n})
    (i : {i : nat | i < S k}),
    ren (lift σ2) (lift_bind σ1 i) =
    lift_bind (ren σ2 ∘ σ1) i.
Proof.
  intros k m n σ1 σ2 i.
  unfold lift_bind.
  destruct (lt_dec _ _) as [|Hge].
  + rewrite !ren_comp.
    apply ren_ext, lift_weaken.
  + simpl. f_equal.
    apply sig_lt_ext.
    simpl.
    apply lift_eq.
Qed.

Lemma ren_bind :
  ∀ {k m n : nat}
    (σ1 : {i | i < k} → term m)
    (σ2 : {i | i < m} → {i | i < n})
    (t : term k),
  ren σ2 (bind σ1 t) = bind (ren σ2 ∘ σ1) t.
Proof.
  fix IH 6.
  intros k m n σ1 σ2 t.
  destruct t; simpl; try reflexivity.
  - rewrite IH.
    f_equal.
    rewrite IH.
    apply bind_ext.
    intros i.
    apply lift_bind_ren.
  - rewrite !IH.
    f_equal.
    apply bind_ext.
    intros i.
    apply lift_bind_ren.
  - now rewrite !IH.
Qed. 

Lemma bind_weaken :
  ∀ {k n : nat}
    (σ : {i | i < k} → term n)
    (t : term k),
  bind (lift_bind σ) (ren weaken t) = ren weaken (bind σ t).
Proof.
  fix IH 4.
  intros k n σ t.
  destruct t; simpl.
  - apply lift_bind_weaken.
  - rewrite IH.
    f_equal.
    rewrite ren_bind, bind_ren.
    apply bind_ext.
    intros i.
    rewrite lift_bind_ren, lift_bind_lift.
    apply lift_bind_ext.
    intros j.
    apply lift_bind_weaken.
  - rewrite IH.
    f_equal.
    rewrite ren_bind, bind_ren.
    apply bind_ext.
    intros i.
    rewrite lift_bind_ren, lift_bind_lift.
    apply lift_bind_ext.
    intros j.
    apply lift_bind_weaken.
  - now rewrite !IH.
  - reflexivity.
Qed.

Lemma lift_bind_comp :
  ∀ {k m n : nat}
  (σ1 : {i | i < k} → term m)
  (σ2 : {i | i < m} → term n)
  (i : {i | i < S k}),
  bind (lift_bind σ2) (lift_bind σ1 i) = lift_bind (bind σ2 ∘ σ1) i.
Proof.
  intros k m n σ1 σ2 i.
  unfold lift_bind at 2 3.
  destruct (lt_dec _ _) as [Hge | Hlt].
  - rewrite ren_bind, bind_ren.
    apply bind_ext.
    apply lift_bind_weaken.
  - simpl.
    unfold lift_bind.
    destruct (lt_dec _ _) as [Hge | Hlt']; [simpl in Hge; lia|].
    reflexivity.
Qed.

Lemma bind_comp :
  ∀ {k m n : nat}
  (σ1 : {i | i < k} → term m)
  (σ2 : {i | i < m} → term n)
  (t : term k),
  bind σ2 (bind σ1 t) = bind (bind σ2 ∘ σ1) t.
Proof.
  fix IH 6.
  intros k m n σ1 σ2 t.
  destruct t; simpl; try reflexivity.
  1,2 :
    rewrite !IH;
    f_equal;
    apply bind_ext;
    intros i;
    apply lift_bind_comp.
  now rewrite !IH.
Qed.

(* Basic substitution capturing the free variable introduced last *)
Definition bind_first {k : nat} (t : term k) (i : {i | i < S k}) : term k
  :=
  match lt_dec (proj1_sig i) k with
  | left Hi => Var (exist _ (proj1_sig i) Hi)
  | right _ => t
  end.
