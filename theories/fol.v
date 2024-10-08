Require Import ssreflect ssrbool Nat.
Require Import BinNat.
Require BinPos Ndec.
Require Export Ring List.
Require Import Lia.

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

Fixpoint tlift i j t :=
  match t with
  | tapp f l =>
      tapp f (map (tlift i j) l)
  | tdb k =>
      if (k <? i)
      then t
      else tdb (j + k)
  end.

Fixpoint lift i j A :=
  match A with
  | fbot => A
  | ftop => A
  | fatom R l => fatom R (map (tlift i j) l)
  | fconj A B => fconj (lift i j A)(lift i j B)
  | fdisj A B => fdisj (lift i j A)(lift i j B)
  | fimp A B => fimp (lift i j A)(lift i j B)
  | ffa A => ffa (lift (S i) j A)
  | fex A => fex (lift (S i) j A)
  end.

Fixpoint tsubst i u t :=
  match t with
  | tapp f l =>
      tapp f (map (tsubst i u) l)
  | tdb j =>
      if (i =? j)
      then u
      else if (i <? j)
           then tdb (j - 1)
           else tdb j
  end.

Fixpoint subst i u A :=
  match A with
  | fbot => A
  | ftop => A
  | fatom R l => fatom R (map (tsubst i u) l)
  | fconj A B => fconj (subst i u A)(subst i u B)
  | fdisj A B => fdisj (subst i u A)(subst i u B)
  | fimp A B => fimp (subst i u A)(subst i u B)
  | ffa A => ffa (subst (S i) (tlift 0 1 u) A)
  | fex A => fex (subst (S i) (tlift 0 1 u) A)
  end.

Lemma tsubst_lift : forall t u i, tsubst i u (tlift i 1 t) = t.
  fix HR 1.
  case => [k | f l] u i /=.
  case ki : (_ <? _) => /=;
   move/PeanoNat.Nat.leb_spec0: ki => ki;
     case e : (_ =? _) => //=;
     move/PeanoNat.Nat.eqb_spec: e => e; try lia;                     case ik : (_ <? _) => /=;
   move/PeanoNat.Nat.leb_spec0: ik => //= ik; try lia.
  by rewrite PeanoNat.Nat.sub_0_r.
replace (map (tsubst i u) (map (tlift i 1) l)) with l;
    first done.
elim: l => [| v l Hl] //=.
by rewrite HR -Hl.  
Qed.

Lemma tlift0 : forall t j, tlift j 0 t = t.
fix HR 1.
case => [i | f l] j /=.
  by case: (_ <? _).
replace (map (tlift j 0) l) with l; first done.
elim: l => [//=|t l Hl]/=.
by rewrite -Hl HR.
Qed.


Lemma tlift_lift0 : forall t i j, tlift 0 i (tlift 0 j t) = tlift 0 (i+j) t.
fix HR 1.
case => [k | f l] i j //=.
  by rewrite PeanoNat.Nat.add_assoc.
replace  (map (tlift 0 i) (map (tlift 0 j) l))
         with  (map (tlift 0 (i + j)) l); first done.
elim: l => [//= | u l /= ->].
by rewrite HR.
Qed.

Lemma ltlift_lift0 : forall l i j,
   map (tlift 0 i) (map (tlift 0 j) l) = map (tlift 0 (i+j)) l.
by elim => [//= | t l /= Hl] i j; rewrite tlift_lift0 Hl.
Qed.
  
Lemma tlift_lift : forall t j,
    tlift (S j) 1 (tlift 0 1 t) = tlift 0 1 (tlift j 1 t).
fix HR 1.
case => [i | f l]/= j.
 case ij: (_ <? _); move/PeanoNat.Nat.leb_spec0: ij => ij;
  case ij': (_ <? _); move/PeanoNat.Nat.leb_spec0: ij' => ij' //=;
    lia.
replace (map (tlift (S j) 1) (map (tlift 0 1) l))
        with (map (tlift 0 1) (map (tlift j 1) l)); first done.
elim: l => [//=| u l /= ->].
by rewrite HR.
Qed.


Lemma tlift_lift' : forall t j k,
    tlift (S (j+k)) 1 (tlift  k 1 t) = tlift k 1 (tlift (j+k) 1 t).
fix HR 1.
case => [i | f l]/= j k.
  case ik: (_ <? _); move/PeanoNat.Nat.leb_spec0: ik => ik;
                                                        case ij: (_ <? _); move/PeanoNat.Nat.leb_spec0: ij => ij;
                                                                                                              try lia; simpl;
                                case ijk: (_ <? _); move/PeanoNat.Nat.leb_spec0: ijk => ijk; try lia;
                        case ik': (_ <? _); move/PeanoNat.Nat.leb_spec0: ik' => ik' //=; try lia.
replace (map (tlift (S (j + k)) 1) (map (tlift k 1) l))
        with (map (tlift k 1) (map (tlift (j + k) 1) l)); first done.
by elim: l => [//=| t l /= ->]; rewrite HR.
Qed.



Lemma ltlift_tlift j : forall l,
    map (tlift (S j) 1)(map (tlift 0 1) l) =
      map (tlift 0 1)(map (tlift j 1) l).
elim => [//= | t l /= ->].
by rewrite tlift_lift.
Qed.


Lemma ltlift_tlift' j k : forall l,
    map (tlift (S (j+k)) 1)(map (tlift k 1) l) =
      map (tlift k 1)(map (tlift (j+k) 1) l).
elim => [//= | t l /= ->].
by rewrite tlift_lift'.
Qed.

Lemma lift_lift : forall A j k,
    lift (S (j+k)) 1 (lift k 1 A) = lift k 1 (lift (j+k) 1 A).
fix HR 1.
case => [X l | A B | A B | A B | //= | //= | A | A] j k /=;
                                        try by (rewrite !HR).
- by rewrite ltlift_tlift'.
- move: (HR A j (S k));
    rewrite PeanoNat.Nat.add_succ_r.
  by move ->.
- move: (HR A j (S k));
    rewrite PeanoNat.Nat.add_succ_r.
  by move ->.
Qed.

Lemma tlift_lift_i :
  forall t i j k,
    tlift i j (tlift i k t) = tlift i (j+k) t.
fix HR 1.
case => [n | f l]/= i j k.
- case ni: (_<?_); move/PeanoNat.Nat.leb_spec0: ni => ni/=;
   case ni': (_<?_); move/PeanoNat.Nat.leb_spec0: ni' => ni'//=;
   try lia.
  by rewrite PeanoNat.Nat.add_assoc.
- replace  (map (tlift i j) (map (tlift i k) l))
       with (map (tlift i (j + k)) l); first done.
by elim: l => [//=|t l /= ->]; rewrite HR.
Qed.

Lemma lift_lift_i : forall A i j k,
    lift i j (lift i k A) = lift i (j+k) A.
fix HR 1.
case => [X l | A B | A B | A B | //= | //= | A | A] i j k /=;
                                        try by (rewrite !HR).
- replace (map (tlift i j) (map (tlift i k) l))
    with (map (tlift i (j + k)) l); first done.
  by elim: l => [//=|t l /= -> ]; rewrite tlift_lift_i.
Qed.

  
Lemma tcoerce_lift : forall F h g x t,
    tcoerce F (h++x::g) (tlift (length h) 1 t) = tcoerce F (h++g) t.
move => F h g x; fix HR 1.
case => [i | f l]/=.
 case ei : (_ <?_) => //=; move/PeanoNat.Nat.leb_spec0: ei => ei.
   rewrite !app_nth1 //=; lia.
   rewrite !app_nth2; try lia.
   rewrite PeanoNat.Nat.sub_succ_l //=; lia.
replace (map (tcoerce F (h ++ x :: g)) (map (tlift (length h) 1) l)) with (map (tcoerce F (h ++ g)) l); first done.
by elim: l => [//= | t l /= ->]; rewrite HR.
Qed.

Lemma tcoerce_lift' : forall F g h u,
 tcoerce F g u = tcoerce F (h ++ g) (tlift 0 (length h) u).
move => F g h; fix HR 1.
case => [i | f l]/=.
   rewrite !app_nth2; try lia.
   replace (length h + i - length h) with i; first done; lia.
replace (map (tcoerce F g) l) with
  (map (tcoerce F (h ++ g)) (map (tlift 0 (length h)) l));
  first done.
by elim: l => [//= | t l /= ->]; rewrite HR.
Qed.


  
Lemma lcoerce_lift : forall F h g x l,
  (map (tcoerce F (h ++ x :: g)) (map (tlift (length h) 1) l)) = (map (tcoerce F (h ++ g)) l).
move => F h g x; elim => [ //= | t l /= ->].
by rewrite tcoerce_lift.
Qed.

Lemma coerce_lift : forall F P A h g x,
    coerce F P (h++x::g) (lift (length h) 1 A) <-> coerce F P (h++g) A. 
move => F P.
elim => [X l | A HA B HB | A HA B HB | A HA B HB | //= | //= | A HA | A HA] /= h g x.
- by rewrite lcoerce_lift.
-  move: (HA h g x) => [HA1 HA2];
   move: (HB h g x) => [HB1 HB2];
   split; case; auto.
- move: (HA h g x) => [HA1 HA2];
   move: (HB h g x) => [HB1 HB2];
   split; case; auto.
- move: (HA h g x) => [HA1 HA2];
   move: (HB h g x) => [HB1 HB2];
   split; intro H; auto.
- split; intros H y; move: (HA (y::h) g x) => [HA1 HA2];
   [apply HA1 | apply HA2]; apply H.
-   split; intros [y H]; move: (HA (y::h) g x) => [HA1 HA2];
    exists y;
   [apply HA1 | apply HA2]; apply H.
Qed.


Lemma tcst F : forall t u g h,
    tcoerce F (h++(tcoerce F g u)::g) t
    = tcoerce F (h++g) (tsubst (length h) (tlift 0 (length h) u) t).
fix HR 1.
case => [i | f l] u g h /=.
- case hi: (_ =? _); move/PeanoNat.Nat.eqb_spec: hi => hi.
   by rewrite -hi nth_middle -tcoerce_lift'.
  case hi' : (_ <? _) => /=;
    move/PeanoNat.Nat.leb_spec0: hi' => hi'.
    move: hi' hi; case: i => [|i]//=; first lia.
    move => hi _.
    rewrite PeanoNat.Nat.sub_0_r.
    rewrite app_nth2; first lia.
    rewrite app_nth2; first lia.
    rewrite PeanoNat.Nat.sub_succ_l //=; lia.
  rewrite app_nth1;first lia.
  by rewrite app_nth1;first lia.
- replace (map (tcoerce F (h ++ tcoerce F g u :: g)) l)
          with (map (tcoerce F (h ++ g)) (map (tsubst (length h) (tlift 0 (length h) u)) l)); first done.
  elim: l => [| t l Hl]//=.
  by rewrite Hl HR.
Qed.


Lemma tlift_subst :
  forall t u i,
    tsubst i u (tlift i 1 t) = t.
fix HR 1.
case => [j | f l] u i /=.
  case ij : (_ <? _) => //=;
    move/PeanoNat.Nat.leb_spec0: ij => ij; 
    case eij: (_ =? _) => //=;
    move/PeanoNat.Nat.eqb_spec: eij => eij; try lia;
    case nij : (_ <? _);
    move/PeanoNat.Nat.leb_spec0: nij => nij //=; try lia.
  by rewrite PeanoNat.Nat.sub_0_r.
replace (map (tsubst i u) (map (tlift i 1) l)) with l; first done.
elim: l => [//=| t l /= <-].
by rewrite HR.
Qed.


Lemma llift_subst : forall l i u,
      (map (tsubst i u) (map (tlift i 1) l)) = l.
 elim => [//=| t l /= Hl] i u.
 by rewrite Hl tlift_subst.  
Qed.

 Lemma lift_subst :
  forall A u i,
    subst i u (lift i 1 A) = A.
elim => [X l | A HA B HB | A HA B HB | A HA B HB | //= | //= | A HA | A HA] /= u i; try by rewrite HA //= HB.
by rewrite llift_subst.
Qed.



(* atom, conj, disj, imp, bot, top, top, ffa, fex *)
Lemma cst F P : forall A u g h,
     coerce F P (h++(tcoerce F g u)::g) A
 <-> coerce F P (h++g) (subst (length h) (tlift 0 (length h) u) A).
fix HR 1.
case => [X l | A B | A B | A B | //= | //= | A | A] /= u g h;
        try (move: (HR A u g h) => [HRA1 HRA2];
             move: (HR B u g h) => [HRB1 HRB2]).
- replace (map (tcoerce F (h ++ tcoerce F g u :: g)) l)
  with  (map (tcoerce F (h ++ g)) (map (tsubst (length h) (tlift 0 (length h) u)) l))
  ; first by split.
    elim: l => [| v l Hl] //=.
  by rewrite tcst Hl.
- split; move => [hA hB]; split; auto.
- split; (move => [hA | hB]; [left | right]); auto.
- split; move => H1 H2; auto.
- split; move => H x;
    move: (HR A u g (x::h)) => [ H1 H2].
    simpl in H1.
    replace  (tlift 0 1 (tlift 0 (length h) u))
      with  (tlift 0 (S (length h)) u);
      last by rewrite tlift_lift0.
   apply H1.
   apply H.
  apply H2.
  move/(_ x): H => H; rewrite tlift_lift0 in H; apply H.
- split; move => [x Hx]; exists x;
                   move: (HR A u g (x::h)) => [ H1 H2].
  simpl in H1.
  replace  (tlift 0 1 (tlift 0 (length h) u))
    with  (tlift 0 (S (length h)) u);
    last by rewrite tlift_lift0.
  apply H1.
  apply Hx.
apply H2.
rewrite tlift_lift0 in Hx; apply Hx.
Qed.


Fixpoint clift i j G :=
  match G with
  | nil => G
  | A :: G => (lift i j A) :: (clift i j G)
  end.

Lemma clift_lift : forall G j k,
    clift (S (j+k)) 1 (clift k 1 G) = clift k 1 (clift (j+k) 1 G).
elim => [//=|A G /= HG] j k.
by rewrite lift_lift HG.
Qed.

Lemma clift_lift0 : forall G i j, clift 0 i (clift 0 j G) =
                                   clift 0 (i+j) G.
elim => [//=|A G /= HG] j k.
by rewrite lift_lift_i HG.
Qed.


Lemma clift_app : forall G H j k,
    clift j k (G++H) = (clift j k G)++(clift j k H).
 by elim => [//=|A G /= HG] H j k; rewrite HG.
Qed.
  
Lemma lift_nth i j : forall G k,
    nth k (clift i j G) ftop = lift i j (nth k G ftop).
elim => [|A G HG][|k]//=.
Qed.

Inductive NJ : (list form) -> form -> Type :=
| RAxiom : forall G i,  NJ G (nth i G ftop)
| RTop_i : forall G, NJ G ftop
| RBot_e : forall G A, NJ G fbot -> NJ G A
| RImp_i : forall G A B, NJ (A::G) B -> NJ G (fimp A B)
| RImp_e : forall G A B, NJ G A -> NJ G (fimp A B) -> NJ G B
| RConj_i :  forall G A B, NJ G A -> NJ G B -> NJ G (fconj A B)
| RConj_e1 :  forall G A B, NJ G (fconj A B) -> NJ G A
| RConj_e2 :  forall G A B, NJ G (fconj A B) -> NJ G B
| RDisj_i1 : forall G A B, NJ G A -> NJ G (fdisj A B)
| RDisj_i2 : forall G A B, NJ G B -> NJ G (fdisj A B)
| RDisj_e : forall G A B C, NJ G (fdisj A B) ->
                            NJ (A::G) C -> NJ (B::G) C ->
                            NJ G C
| RFA_i : forall G A, NJ (clift 0 1 G) A -> NJ G (ffa A)
| RFA_e : forall G A t, NJ G (ffa A) -> NJ G (subst 0 t A)
| REX_i : forall G A t, NJ G (subst 0 t A) -> NJ G (fex A)
| REX_e : forall G A B, NJ G (fex A) ->
                        NJ (A::(clift 0 1 G)) (lift 0 1 B) ->
                        NJ G B.

Lemma NJ_corr: forall F P G A, NJ G A ->
                     forall g,
                       (forall i, coerce F P g (nth i G ftop)) ->
                       coerce F P g A.
induction 1 => //= g Hg; simpl in *; auto.    
- elim (IHNJ g Hg).
- move => HA; apply (IHNJ g); move => [|i] //=.
- by case: (IHNJ g).
- by case: (IHNJ g).
- by case: (IHNJ1 g Hg) => HH; [apply IHNJ2 | apply IHNJ3];
                           move => [|i].
- move => x.
  move: (IHNJ (x::g)) => h.
  apply h.
  move =>  i;  rewrite lift_nth. 
  case:  (coerce_lift F P (nth i G ftop) nil g x) => [H1 H2].
  by apply H2.
- case: (cst F P A t g nil) => [/= H1 H2].
  rewrite tlift0 in H1.
  auto.
- exists (tcoerce F g t).
  case: (cst F P A t g nil) => [/= H1 H2].
  apply H2.
  rewrite tlift0.
  auto.
- case: (IHNJ1 g Hg) => [x Hx].
case (coerce_lift F P B nil g x) => [H1 H2].
apply H1.
apply IHNJ2.
move => [|i]//=.
rewrite lift_nth.
case (coerce_lift F P (nth i G ftop) nil g x) => [h3 H4].
auto.
Qed.


Ltac toLia :=
  lazymatch goal with
   | [ h : (_ =? _) |- _ ] =>
       move/PeanoNat.Nat.eqb_spec: h => h
   | [ h : (_ =? _)=true |- _ ] =>
       move/PeanoNat.Nat.eqb_spec: h => h
   | [ h : (_ =? _)=false |- _ ] =>
       move/PeanoNat.Nat.eqb_spec: h => h
   | [ h : (_ <? _) |- _ ] =>
       move/PeanoNat.Nat.leb_spec0: h => h
  |  [ h : (_ <? _) = true |- _ ] =>
       move/PeanoNat.Nat.leb_spec0: h => h
  |  [ h : (_ <? _) = false |- _ ] =>
       move/PeanoNat.Nat.leb_spec0: h => h
  end.

Ltac toLiae :=
  match goal with
   | [ h : (_ =? _) |- _ ] =>
       move/PeanoNat.Nat.eqb_spec: h => h
  |  [ h : (_ =? _) = true |- _ ] =>
       move/PeanoNat.Nat.eqb_spec: h => h
      end.

Ltac myLia :=
  repeat toLia; try lia;
  match goal with
  | |- context f [_ =? _] =>
      let e := fresh "e" in
      case e: (_ =? _) => //=;
                            move/PeanoNat.Nat.eqb_spec: e => e
                                                               
  | |- context f [_ <? _] =>
      let e := fresh "e" in
      case e: (_ <? _) => //=;
                            move/PeanoNat.Nat.leb_spec0: e => e
  | |- context f [_ <=? _] =>
      let e := fresh "e" in
      case e: (_ <=? _) => //=;
                            move/PeanoNat.Nat.leb_spec0: e => e
                                                               
                                                               end.
                      

Lemma nil_app A : forall l1 (a:A) l2,
    (l1 ++ a :: nil) ++ l2 = l1 ++ a :: l2.
elim => [//= | x l1 Hl1] a l2 /=.
by rewrite Hl1.
Qed.

Lemma Weak_aux : forall G A, NJ G A -> forall B D H,
     G = D++H -> NJ (D++B::H) A.
induction 1; intros E D H' ->.
- case id: (i <? (length D)).
   move: (RAxiom (D++E::H') i).
   by rewrite !app_nth1; try myLia.
  replace (nth i (D++H') ftop)
    with (nth (S i) ((D++E::nil)++H') ftop).
    rewrite nil_app; apply RAxiom.
  case id': ((S i) <? (length (D++E::nil))).
  rewrite app_length /= in id'; myLia.  
  rewrite /= !app_nth2; try myLia.
  rewrite app_length.
  replace  (S i - (length D + length (E :: nil)))
    with (i - length D); first done.
  replace (length (E :: nil)) with 1; last done.
  myLia.  
- by constructor.
- by constructor; apply IHNJ.
- apply RImp_i.
  replace  (A :: D ++ E :: H')
           with ((A::D) ++ E :: H'); last done.
  by apply IHNJ.
- apply RImp_e with A; auto.
- apply RConj_i; auto.
- eapply RConj_e1; auto.
- eapply RConj_e2; auto.
- eapply RDisj_i1; auto.
- eapply RDisj_i2; auto.
- apply (RDisj_e _ A B C); auto; rewrite app_comm_cons; auto.
- move: H => h.
  move: H' IHNJ h => H IHNJ h.
  move: (IHNJ (lift 0 1 E) (clift 0 1 D) (clift 0 1 H)) => IH. 
  have hh: (clift 0 1 (D ++ H) = clift 0 1 D ++ clift 0 1 H);
    first by rewrite clift_app.
  move/(_ hh) : IH {hh} => IH.
  apply RFA_i.
  move: IH; rewrite !clift_app //=.
- apply RFA_e; auto.
- apply REX_i with t; auto.
- rewrite clift_app in IHNJ2.
  move: (IHNJ2 (lift 0 1 E)
               (A :: (clift 0 1 D))(clift 0 1 H')(refl_equal _))
      => /= h.
 apply REX_e with A; auto.
 rewrite clift_app //=.
Qed.

Lemma Weak : forall G A, forall B D,
    NJ (D++G) A ->  NJ (D++B::G) A.
move => G A B D d.
 by move: (Weak_aux (D++G) A d B D G (refl_equal _)).
Defined.

Lemma Weak_app : forall G A D,
    NJ G A -> NJ (D++G) A.
move => G A; elim => [//=|B D HD] /= HA.
apply (Weak (D++G) A B nil); auto.
Defined.

Lemma Weak_cons : forall G A B,
    NJ G A -> NJ (B::G) A.
move => G A B.
apply (Weak G A B nil).
Defined.

Lemma tlift_comm : forall i t,
    tlift (S i) 1 (tlift 0 1 t) = tlift 0 1 (tlift i 1 t).
move => i; fix HR 1.
move => [j | f l]//=.
- case ij1: (_<?_);
   move/PeanoNat.Nat.leb_spec0: ij1 => ij1 //=;
  case ij2: (_<?_);
   move/PeanoNat.Nat.leb_spec0: ij2 => ij2 //=; try lia.
- replace  (map (tlift (S i) 1) (map (tlift 0 1) l))
    with  (map (tlift 0 1) (map (tlift i 1) l));
    first done.
by elim: l => [//=|t l /= ->]; rewrite HR.
Qed.

Lemma ltlift_comm : forall i l,
      map (tlift (S i) 1)(map (tlift 0 1) l) =
        map (tlift 0 1) (map (tlift i 1) l).
by move => i; elim => [//=| t l /= ->]; rewrite tlift_comm.
Qed.
  
Lemma lift_comm : forall A i,
    lift (S i) 1 (lift 0 1 A) = lift 0 1 (lift i 1 A).
  elim => [X l | A HA B HB | A HA B HB | A HA B HB
          | //= | //= | A HA| A HA] i //=;
  try by (rewrite HA HB).
- by rewrite ltlift_comm.
- move: (lift_lift A i 1).
  by rewrite PeanoNat.Nat.add_1_r; move -> .  
-  move: (lift_lift A i 1).
  by rewrite PeanoNat.Nat.add_1_r; move -> .  
Qed.

Lemma clift_comm : forall G i,
     clift (S i) 1 (clift 0 1 G) = clift 0 1 (clift i 1 G).
by elim => [//= | A G /= HG] i; rewrite HG lift_comm.     
Qed.

Lemma tlift_tsubst_test : forall k j u i, 
    tlift (k+j) 1 (tsubst k u (tdb i)) =
      tsubst (k) (tlift ( (k+j)) 1 u)
             (tlift (S (k+j)) 1 (tdb i)).
move => k j u i //=.
 case e: (_ =?_); repeat myLia.
move: e   e0 e1 e2 e3 e4 ; case: i => [|i]//=; try lia.
by rewrite PeanoNat.Nat.sub_0_r.
Qed.






  
Lemma tlift_tsubst : forall t k j u, 
    tlift (k+j) 1 (tsubst k u t) =
      tsubst k (tlift (k+j) 1 u)
             (tlift (S (k+j)) 1 t).
fix HR 1.
move => [i | f l] //= j k u. 
- repeat myLia.
  move: e   e0 e1 e2 e3 e4 ; case: i => [|i]//=; try lia.
  by rewrite PeanoNat.Nat.sub_0_r.
- replace  (map (tlift (j + k) 1) (map (tsubst j u) l)) with
    (map (tsubst j (tlift (j + k) 1 u))
         (map (tlift (S (j + k)) 1) l)); first done.
by elim: l => [//=|t l /= ->]; rewrite HR.
Qed.

Lemma ltlift_tsubst : forall l k j u,
    map (tlift (k+j) 1) (map (tsubst k u) l)
    = map (tsubst k (tlift (k+j) 1 u))
          (map (tlift (S (k+j)) 1) l).
elim => [//=|t l /= Hl] k j u.
by rewrite Hl tlift_tsubst.
Qed.

Lemma lift_subst_comm :  forall A k j u, 
    lift (k+j) 1 (subst k u A) =
      subst k (tlift (k+j) 1 u)
             (lift (S (k+j)) 1 A).
  elim => [X l | A HA B HB | A HA B HB | A HA B HB
          | //= | //= | A HA| A HA] k j u //=;
                                    try (by rewrite HA HB).
- by rewrite ltlift_tsubst.
- replace (S (k+j)) with ((S k) + j); last done.
  by rewrite HA -tlift_lift.
- replace (S (k+j)) with ((S k) + j); last done.
  by rewrite HA -tlift_lift.
Qed.

Lemma NJ_lift : forall G A, NJ G A ->
                    forall j, NJ (clift j 1 G)(lift j 1 A).
induction 1 => j; try by constructor.
- rewrite -lift_nth; by constructor.
- apply RImp_i; apply IHNJ.
- apply RImp_e with (lift j 1 A); auto.
- apply RConj_e1 with (lift j 1 B); auto.
- apply RConj_e2 with (lift j 1 A); auto.
- apply RDisj_e with (lift j 1 A)(lift j 1 B); auto.
    apply IHNJ2.
  apply IHNJ3.
- simpl; apply RFA_i.
  replace  (clift 0 1 (clift j 1 G))
    with (clift 0 1 (clift (j+0) 1 G));
   last rewrite PeanoNat.Nat.add_0_r //=.
  rewrite -clift_lift  PeanoNat.Nat.add_0_r.
  apply IHNJ.
- move: (lift_subst_comm A 0 j t) => -> /=.
  by apply RFA_e.
- move: (IHNJ j).
  rewrite (lift_subst_comm A 0 j t) /= => h.
  by apply REX_i with (tlift j 1 t).
- move: (IHNJ2 (S j)) => /= h.
  apply REX_e with (lift (S j) 1 A); first by auto.
  by rewrite lift_comm clift_comm in h.
Defined.


Lemma Subst_aux : forall G B,
    NJ G B ->
      forall A D1 D2, G = (D1++A::D2) -> NJ D2 A -> NJ (D1++D2) B.
induction 1 => A' D1 D2 e HA.
- rewrite e.
  case e1 : (i =? length D1);
    move/PeanoNat.Nat.eqb_spec: e1 => e1 //=.
    rewrite e1 nth_middle.
    by apply Weak_app.
  case e2 : (i <? length D1);
        move/PeanoNat.Nat.leb_spec0: e2 => e2 //=.
    rewrite app_nth1; first lia.
    rewrite -(app_nth1 _ D2); first lia.
    apply RAxiom.
  replace  (nth i (D1 ++ A' :: D2) ftop)
    with (nth (i - 1) (D1 ++ D2) ftop);
    first by apply RAxiom.
  rewrite !app_nth2; try lia.
  replace (A' :: D2) with ((A'::nil)++D2); last done.
  rewrite !app_nth2 //=; first lia.
  replace (i - 1 - length D1)
    with  (i - length D1 - 1); first done.
  lia.
- constructor.
- constructor; eauto.
- apply RImp_i. move:(IHNJ A' (A::D1) D2).
  rewrite e.
  move => h; apply (h (refl_equal _) HA).
- apply RImp_e with A; eauto.
- apply RConj_i; eauto.
- eapply RConj_e1; eauto.
- eapply RConj_e2; eauto.
- apply RDisj_i1; eauto.
- apply RDisj_i2; eauto.
- apply RDisj_e with A B; first eapply IHNJ1; eauto.
    move: (IHNJ2 A' (A::D1) D2).
    rewrite e => h; by apply h.
  move: (IHNJ3 A' (B::D1) D2).
  rewrite e => h; auto.
- apply RFA_i.
  rewrite clift_app.
  apply IHNJ with (lift 0 1 A').
  rewrite e !clift_app //=.     
  move: (IHNJ (lift 0 1 A') nil (clift 0 1 D2)).
  rewrite e clift_app /= => h.
  by apply NJ_lift.
- apply RFA_e.
  by apply IHNJ with A'.
- apply REX_i with t.
  by apply IHNJ with A'.
- apply REX_e with A; first by eauto.
  move: (IHNJ2 (lift 0 1 A') (A::(clift 0 1 D1)) (clift 0 1 D2)).
  rewrite e !clift_app /= => h.
  apply h; first done.
  by  apply NJ_lift.
Defined.

Lemma Subst : forall  B A D1 D2,
    NJ (D1++A::D2) B ->
       NJ D2 A -> NJ (D1++D2) B.
move => B A D1 D2 d1 d2.
exact (Subst_aux (D1++A::D2) B d1 A D1 D2 (refl_equal _) d2).
Defined.


Inductive Deriv :=
  deriv : forall G A, NJ G A -> Deriv.

Definition subDeriv : forall (l : list nat) G A,
    NJ G A -> Deriv.
elim => [/= | b l Hl] G A d.
  exact (deriv G A d).
case: d => [D i | D | D B d | D B C d | D B C d1 d2  |
             D B C d1 d2 | D B C d | D B C d | D B C d |
             D B1 B2 d | D B1 B2 C d1 d2 d3 | D B d
           | D B C d | D B C d | D B C d1 d2 ].
- exact (deriv _ _ (RAxiom D i)).
- exact (deriv _ _ (RTop_i D)).
- exact (Hl D _ d).
- exact (Hl _ _ d).
- case: b => [|_].
   exact (Hl _ _ d1).  
  exact (Hl _ _ d2).
- case: b => [|_].
   exact (Hl _ _ d1).  
  exact (Hl _ _ d2).
- exact (Hl _ _ d).
- exact (Hl _ _ d).
- exact (Hl _ _ d).
- exact (Hl _ _ d).
- case: b => [|[|_]].
     exact (Hl _ _ d1).
    exact (Hl _ _ d2).
  exact (Hl _ _ d3).
- exact (Hl _ _ d).
- exact (Hl _ _ d).
- exact (Hl _ _ d).
- case: b => [|_].
   exact (Hl _ _ d1).  
  exact (Hl _ _ d2).
Defined.

Definition is_intro G A (d:NJ G A) : bool :=
  match d with
  | RConj_i _ _ _ _ _ => true
  | RDisj_i1 _ _ _ _ => true
  | RDisj_i2 _ _ _ _ => true
  | RImp_i _ _ _ _ => true
  | RFA_i _ _ _ => true
  | REX_i _ _ _ _ => true
  | RTop_i _ => true
  | _ => false
  end.

