
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
      move/PeanoNat.Nat.eqb_spec: e => e; try lia;
      case ik : (_ <? _) => /=;
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


Lemma tcoerce_lift : forall F h g x t,
    tcoerce F (h++x::g) (tlift (length h) 1 t) = tcoerce F (h++g) t.
move => F h g x; fix HR 1.
case => [i | f l]/=.
 case ei : (_ <?_) => //=; move/PeanoNat.Nat.leb_spec0: ei => ei.
   rewrite !app_nth1 //=; lia.
   rewrite !app_nth2; try lia.
   rewrite PeanoNat.Nat.sub_succ_l //=; lia.
replace (map (tcoerce F (h ++ x :: g)) (map (tlift (length h) 1) l))
  with (map (tcoerce F (h ++ g)) l); first done.
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
    with (map (tcoerce F (h ++ g)) (map (tsubst (length h) (tlift 0 (length h) u)) l));
    first done.
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
   elim => [X l | A HA B HB | A HA B HB | A HA B HB | //= | //= | A HA | A HA] /= u i;
           try by rewrite HA //= HB.
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
    with  (tlift 0 (S (length h)) u).
apply H1.
  apply H.
by rewrite lift_lift.
apply H2.
move/(_ x): H => H; rewrite lift_lift in H; apply H.
- split; move => [x Hx]; exists x;
                   move: (HR A u g (x::h)) => [ H1 H2].
  simpl in H1.
  replace  (tlift 0 1 (tlift 0 (length h) u))
    with  (tlift 0 (S (length h)) u).
apply H1.
  apply Hx.
by rewrite lift_lift.
apply H2.
 rewrite lift_lift in Hx; apply Hx.
Qed.


Fixpoint clift i j G :=
  match G with
  | nil => G
  | A :: G => (lift i j A) :: (clift i j G)
  end.

Lemma clift_lift' : forall G j k,
    clift (S (j+k)) 1 (clift k 1 G) = clift k 1 (clift (j+k) 1 G).
elim => [//=|A G /= HG] j k.
by rewrite lift_lift' HG.
Qed.

Lemma clift_lift : forall G i j, clift 0 i (clift 0 j G) =
                                   clift 0 (i+j) G.
elim => [//=|A G /= HG] j k.
by rewrite lift_lift HG.
Qed.



Lemma clift_app : forall G H j k, clift j k (G++H) = (clift j k G)++(clift j k H).
 by elim => [//=|A G /= HG] H j k; rewrite HG.
Qed.
  
Lemma lift_nth i j : forall G k,
    nth k (clift i j G) ftop = lift i j (nth k G ftop).
elim => [|A G HG][|k]//=.
Qed.

