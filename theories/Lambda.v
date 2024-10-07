From Autosubst Require Import Autosubst.

Check subst_comp.

Inductive term : Type :=
| Var (n : nat)
| App (s t : term)
| Lam (s : {bind term}).
