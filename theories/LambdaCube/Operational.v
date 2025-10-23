From Coq Require Import Utf8.
From FormArith Require Import Base.
From FormArith.LambdaCube Require Import Term.

Inductive head_step {n : nat} : term n → term n → Prop :=
| beta_red
    (ty : term n)
    (body : term (S n))
    (arg : term n) : head_step (App (Abs ty body) arg) (bind (bind_first arg) body).

Inductive step {n : nat} : term n → term n → Prop :=
| ctx_red (K : ctx n) (t u : term n) :
  head_step t u → step (fill K t) (fill K u).
