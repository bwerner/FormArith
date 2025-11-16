From Coq Require Import Utf8.
From Coq Require Import Arith Lia.
From FormArith Require Import Base.
From FormArith.LambdaCube Require Import Term Operational.

Inductive typing_ctx n : nat -> Type :=
| empty : typing_ctx n 0
| cons {l} : typing_ctx n l -> term n -> typing_ctx n (S l).

Arguments empty {n}.
Arguments cons {n l}.

Notation "\" := empty.

Fixpoint kth_index_ctx {n l} (Γ: typing_ctx n l) k {struct Γ} : k < l -> term n :=
  match Γ in typing_ctx _ l return k < l -> term n with
  | \ => fun H => match Nat.nlt_0_r _ H with end
  | @cons _ l Γ t =>
      match k return k < S l -> term n with
      | 0 => fun _ => t
      | S k => fun (H: S k < S l) => kth_index_ctx Γ k (le_S_n _ _ H)
      end
  end
.

Fixpoint map_ctx {n m l} (f: term n -> term m) (Γ: typing_ctx n l) : typing_ctx m l :=
  match Γ with
  | \ => \
  | cons Γ t => cons (map_ctx f Γ) (f t)
  end.

Definition slide {n} (i : {k | k < n}) : {k | k < S n} :=
  exist _ (S (proj1_sig i)) (le_n_S _ _ (proj2_sig i)).

Definition cons' {n} (Γ : typing_ctx n n) (t: term n) : typing_ctx (S n) (S n) :=
  cons (map_ctx (ren slide) Γ) (ren slide t).

Notation "A , t" := (cons' A t) (at level 61, left associativity, t at next level).

Definition pi_scheme := sort -> sort -> bool.

Definition pi_scheme_check (P: pi_scheme) (s s': sort) : Prop := P s s' = true.

Reserved Notation "A ⊢( P ) s ':' t"
  (at level 70, s at next level, t at next level, P at next level).
Reserved Notation "A ⊢( P )" (at level 70, P at next level).

Inductive typing (P: pi_scheme) : forall {n}, typing_ctx n n -> term n -> term n -> Prop :=
| typ_star {n} {Γ: typing_ctx n n} : Γ ⊢(P) -> Γ ⊢(P) Srt Star : Srt Box
| typ_var {n} {Γ: typing_ctx n n} {i} :
  Γ ⊢(P) -> Γ ⊢(P) Var i : kth_index_ctx Γ (proj1_sig i) (proj2_sig i)
| typ_pi {n} {Γ: typing_ctx n n} {A B s s'} :
  pi_scheme_check P s s' -> Γ ⊢(P) A : Srt s -> Γ, A ⊢(P) B : Srt s' -> Γ ⊢(P) Pi A B : Srt s'
| typ_abs {n} {Γ: typing_ctx n n} {A B s s' t} :
  pi_scheme_check P s s' ->
  Γ ⊢(P) A : Srt s ->
  Γ, A ⊢(P) B : Srt s' ->
  Γ, A ⊢(P) t : B ->
  Γ ⊢(P) Abs A t : Pi A B
| typ_app {n} {Γ: typing_ctx n n} {A B t u} :
  Γ ⊢(P) t : Pi A B -> Γ ⊢(P) u : A -> Γ ⊢(P) App t u : bind (bind_first u) B
| typ_conv {n} {Γ: typing_ctx n n} {t A B} :
  Γ ⊢(P) t : A -> A ≅ B -> Γ ⊢(P) t : B
with ctx_wf (P: pi_scheme) : forall {n}, typing_ctx n n -> Prop :=
| empty_wf : \ ⊢(P)
| cons_wf {n} {A: typing_ctx n n} {t: term n} {s} :
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

Notation "'PF'" := systemP.

Definition P_weak_omega : pi_scheme :=
  fun s s' => is_star s || is_box s'.

Notation "'Pwω'" := P_weak_omega.

Definition CoC : pi_scheme :=
  fun s s' => true.

Notation "'C'" := CoC.
