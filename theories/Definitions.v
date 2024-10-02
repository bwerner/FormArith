Require Import List.

Inductive term :=
| tdb : nat -> term
| tapp : nat -> list term -> term.

Inductive form :=
| fatom : nat -> list term -> form
| fconj : form -> form -> form
| fdisj : form -> form -> form
| fimp : form -> form -> form
| fbot : form
| ftop : form
| ffa : form -> form
| fex : form -> form.

Fixpoint tcoerce (F : nat -> list nat -> nat)
         (g : list nat) (t : term) : nat :=
  match t with
  | tdb i => nth i g 0
  | tapp f l => F f (map (tcoerce F g) l)
  end.

Fixpoint coerce (F : nat -> list nat -> nat)
         (P : nat -> list nat -> Prop) (g : list nat)
         (A : form) : Prop :=
  match A with
  | fbot => False
  | ftop => True
  | fatom R l => P R (map (tcoerce F g) l)
  | fconj A B => (coerce F P g A)/\(coerce F P g B)
  | fdisj A B => (coerce F P g A)\/(coerce F P g B)
  | fimp A B => (coerce F P g A)->(coerce F P g B)
  | ffa A => forall x, coerce F P (x::g) A
  | fex A => exists x, coerce F P (x::g) A 
  end.
