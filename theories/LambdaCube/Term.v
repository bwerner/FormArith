From Coq Require Import Utf8.
From Coq Require Import Arith Lia.

Inductive sort : Type :=
| Star : sort
| Box : sort.

Inductive term (n : nat) : Type :=
| Var : {k | k < n} → term n
| Pi : term n → term (S n) → term n
| Abs : term n → term (S n) → term n
| App : term n → term n → term n
| Srt : sort → term n
.

Arguments Var {n}.
Arguments Pi {n}.
Arguments Abs {n}.
Arguments App {n}.
Arguments Srt {n}.

Definition weaken {k : nat} (i : {i | i < k}) : {i | i < S k} :=
  exist _ (proj1_sig i) (Nat.lt_lt_succ_r _ _ (proj2_sig i)).

Definition lift
  {k n : nat} (σ : {i | i < k} → {i | i < n})
  (i : {i | i < S k}) : {i | i < S n}
  :=
  match lt_dec (proj1_sig i) k with
  | left Hi => weaken (σ (exist _ (proj1_sig i) Hi))
  | right _ => exist _ n (Nat.lt_succ_diag_r n)
  end.

Lemma sig_lt_ext {k : nat} (p q : {i | i < k}) :
  proj1_sig p = proj1_sig q → p = q.
Proof.
  destruct p, q.
  simpl.
  intros ->.
  f_equal.
  apply le_unique.
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

Fixpoint subst {k n : nat} (σ : {i | i < k} → {i | i < n}) (t : term k) : term n :=
  match t with
  | Var i => Var (σ i)
  | Pi ty fam => Pi (subst σ ty) (subst (lift σ) fam)
  | Abs ty tm => Abs (subst σ ty) (subst (lift σ) tm)
  | App tm1 tm2 => App (subst σ tm1) (subst σ tm2)
  | Srt s => Srt s
  end.

Definition lift_bind {k n : nat} (σ : {i | i < k} → term n) (i : {i | i < S k}) : term (S n) :=
  match lt_dec (proj1_sig i) k with
  | left Hi => subst weaken (σ (exist _ (proj1_sig i) Hi))
  | right _ => Var (exist _ n (Nat.lt_succ_diag_r n))
  end.
 
Fixpoint bind {k n : nat} (σ : {i | i < k} → term n) (t : term k) : term n
  :=
  match t with
  | Var i => σ i
  | Pi ty fam => Pi (bind σ ty) (bind (lift_bind σ) fam)
  | Abs ty tm => Abs (bind σ ty) (bind (lift_bind σ) tm)
  | App tm1 tm2 => App (bind σ tm1) (bind σ tm2)
  | Srt s => Srt s
  end.

Definition bind_first {k : nat} (t : term k) (i : {i | i < S k}) : term k
  :=
  match lt_dec (proj1_sig i) k with
  | left Hi => Var (exist _ (proj1_sig i) Hi)
  | right _ => t
  end.

Inductive conv {n : nat} : term n → term n → Prop :=
| conv_var (k : {k | k < n}) : conv (Var k) (Var k)
| conv_srt (s : sort) : conv (Srt s) (Srt s)
| conv_pi (A1 A2 : term n) (B1 B2 : term (S n)) :
  conv A1 A2 → conv B1 B2 → conv (Pi A1 B1) (Pi A2 B2)
| conv_abs (A1 A2 : term n) (B1 B2 : term (S n)) :
  conv A1 A2 → conv B1 B2 → conv (Abs A1 B1) (Abs A2 B2)
| conv_app (A1 A2 B1 B2 : term n) :
  conv A1 A2 → conv B1 B2 → conv (App A1 B1) (App A2 B2)
| conv_redex_l (A1 A2 A3 : term n) (B : term (S n)) :
  conv (bind (bind_first A2) B) A3 → conv (App (Abs A1 B) A2) A3
| conv_redex_r (A1 A2 A3 : term n) (B : term (S n)) :
  conv A3 (bind (bind_first A2) B) → conv A3 (App (Abs A1 B) A2)
.
