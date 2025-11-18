From Coq Require Import Utf8.
From Coq Require Import Arith Lia.
From FormArith Require Import Base.
From FormArith.LambdaCube Require Import Term Operational Typing.

Inductive SN {n : nat} (t : term n) : Prop :=
| SN_on : (∀ u, t ≻ u → SN u) → SN t.

Lemma typing_SN {Sc : pi_scheme} {n : nat} (Γ : typing_ctx n) (t A : term n) :
  Γ ⊢(Sc) t : A → SN t.
Admitted.
