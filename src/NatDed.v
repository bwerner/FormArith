
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

Lemma Weak_aux : forall G A, NJ G A -> forall B D H,
     G = D++H -> NJ (D++B::H) A.
induction 1; intros E D H' ->.
- elim triche.
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
  assert (clift 0 1 (D ++ H) = clift 0 1 D ++ clift 0 1 H);
    first by rewrite clift_app.
move/(_ H0) : IH {H0} => IH.
apply RFA_i.
 move: IH; rewrite !clift_app //=.
- apply RFA_e; auto.
- apply REX_i with t; auto.
- rewrite clift_app in IHNJ2.
  move: (IHNJ2 (lift 0 1 E) (A :: (clift 0 1 D))(clift 0 1 H')(refl_equal _)) => /= h.
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
