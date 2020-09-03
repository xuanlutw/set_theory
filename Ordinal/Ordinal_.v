Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Nat.
Require Import Ordinal.Order.
Require Import Ordinal.Transfinite.

(* Epsilon *)
Theorem eps_exist: ∀ R, ∀ A, ∃ E, wo R A
  → fn E ∧ dom(E) = A ∧ (∀ t, t ∈ A → E[t] = E⟦seg R A t⟧).
Proof.
  intros R A.
  destruct (LEM (wo R A)) as [P1 | P1].
  + assert ((∀ x, ∃ y, y = ran(x)) ∧  
      (∀ x, ∀ y1, ∀ y2, y1 = ran(x) → y2 = ran(x) → y1 = y2)) as P2.
    { split.
      + intros x.
        exists (ran(x)).
        apply eq_r.
      + intros x y1 y2 P2 P3.
        apply (eq_cr (λ x, y1 = x) P3).
        apply P2. }
    destruct (transfinite_recursion (λ x, λ y, y = ran(x)) _ _ P1 P2) 
      as [E [P3 [P4 P5]]].
    exists E.
    intros _.
    split.
    - apply P3.
    - split.
      * apply P4.
      * apply P5.
  + exists R.
    intros P2.
    apply bot_e.
    apply (P1 P2).
Qed.

Definition eps (R A: J)       := (ex_outl (eps_exist R A)).
Notation   "E( R , A )"       := (eps R A).
Definition eps_image (R A: J) := (ran(E(R, A))).
Notation   "EI( R , A )"      := (eps_image R A).
Definition eps_rel (R A: J) := 
  {s: (EI(R, A)) ⨉ (EI(R, A))| ∃ x, ∃ y, s = ⟨x, y⟩ ∧ x ∈ y}.
Notation   "ER( R , A )"    := (eps_rel R A).

Lemma eps_fn: ∀ R, ∀ A, wo R A → fn (E(R, A)).
Proof.
  intros R A P1.
  destruct (ex_outr (eps_exist R A) P1) as [P3 [P4 P5]].
  apply P3.
Qed.

Lemma eps_dom: ∀ R, ∀ A, wo R A → dom(E(R, A)) = A.
Proof.
  intros R A P1.
  destruct (ex_outr (eps_exist R A) P1) as [P3 [P4 P5]].
  apply P4.
Qed.

Lemma eps_fnm: ∀ R, ∀ A, wo R A → fnm (E(R, A)) A (EI(R, A)).
Proof.
  intros R A P1.
  split.
  + apply (eps_fn _ _ P1).
  + split.
    - apply (eps_dom _ _ P1).
    - apply sub_r.
Qed.

Lemma eps_e1: ∀ R, ∀ A, ∀ t, wo R A → t ∈ A → E(R, A)[t] = E(R, A)⟦seg R A t⟧.
Proof.
  intros R A t P1 P2.
  destruct (ex_outr (eps_exist R A) P1) as [P3 [P4 P5]].
  apply (P5 _ P2).
Qed.

Lemma eps_e2: ∀ R, ∀ A, ∀ t, ∀ s, wo R A → t ∈ A → s ∈ E(R, A)[t] →
  ∃ y, s = E(R, A)[y] ∧ y ∈ A ∧ y <[R] t.
Proof.
  intros R A t s P1 P2 P3.
  destruct (image_e _ _ _ (eq_cl (λ x, s ∈ x) (eps_e1 _ _ _ P1 P2) P3))
    as [y [P4 P5]].
  exists y.
  split.
  + apply (fval_i).
    - apply (eps_fn _ _ P1).
    - apply P4.
  + split.
    - apply (seg_e1 _ _ _ _ P2 P5).
    - apply (seg_e2 _ _ _ _ P2 P5).
Qed.

Lemma eps_in_i: ∀ R, ∀ A, ∀ t1, ∀ t2, wo R A → t1 ∈ A → t2 ∈ A → t1 <[R] t2
  → (E(R, A))[t1] ∈ (E(R, A))[t2].
Proof.
  intros R A x y P1 P2 P3 P4.
  apply (eq_cr (λ y, (E(R, A))[x] ∈ y) (eps_e1 _ _ _ P1 P3)).
  apply image_i.
  exists x.
  split.
  + apply fval_i2.
    apply (eps_fn _ _ P1).
    apply (eq_cr (λ y, x ∈ y) (eps_dom _ _ P1)).
    apply P2.
  + apply (seg_i _ _ _ _ P2 P4).
Qed.

Lemma eps_a: ∀ R, ∀ A, ∀ t, wo R A → t ∈ A → (E(R, A))[t] ∉  (E(R, A))[t].
Proof.
  intros R A t P1 P2.
  pose ({x: A| E(R, A)[x] ∈ E(R, A)[x]}) as S.
  destruct (LEM (S = ∅)) as [P3 | P3].
  + apply (sub_empty _ _ _ P3 P2).
  + destruct (wo_least_prop _ _ P1 _ (sub_e1 _ _) P3) as [x [Q1 Q2]].
    destruct (sub_e _ _ _ Q1) as [Q3 Q4].
    assert (E(R, A)[x] ∈ E(R, A)⟦seg R A x⟧) as Q5.
    { apply (eq_cl (λ y, E(R, A)[x] ∈ y) (eps_e1 R A x P1 Q3)).
      apply Q4. }
    destruct (image_e _ _ _ Q5) as [y [Q6 Q7]].
    destruct (sub_e _ _ _ Q7) as [Q8 Q9].
    apply bot_e.
    apply (wo_nle_i _ _ _ _ P1 Q8 Q3 Q9).
    apply (Q2 y).
    apply sub_i.
    - apply Q8.
    - apply (eq_cl (λ x, x ∈ x) (fval_i _ _ _ (eps_fn _ _ P1) Q6)).
      apply Q4.
Qed.

Lemma eps_sing_rot: ∀ R, ∀ A, wo R A → sing_rot (E(R, A)).
Proof.
  intros R A P1 a1 a2 b P2 P3.
  pose (eq_cl (λ x, a1 ∈ x) (eps_dom _ _ P1) (dom_i2 _ _ _ P2)) as P4.
  pose (eq_cl (λ x, a2 ∈ x) (eps_dom _ _ P1) (dom_i2 _ _ _ P3)) as P5.
  destruct (wo_tricho_weak _ _ P1 _ _ P4 P5) as [Q1 | [Q1 | Q1]].
  - pose (eps_in_i _ _ _ _ P1 P4 P5 Q1) as Q2.
    apply bot_e.
    apply (eps_a _ _ _ P1 P5).
    pose (eq_cr (λ x, x ∈ E(R, A)[a2]) (fval_i _ _ _ (eps_fn _ _ P1) P2) Q2)
      as Q3.
    apply (eq_cl (λ x, x ∈ E(R, A)[a2]) (fval_i _ _ _ (eps_fn _ _ P1) P3) Q3).
  - apply Q1.
  - pose (eps_in_i _ _ _ _ P1 P5 P4 Q1) as Q2.
    apply bot_e.
    apply (eps_a _ _ _ P1 P5).
    pose (eq_cr (λ x, E(R, A)[a2] ∈ x) (fval_i _ _ _ (eps_fn _ _ P1) P2) Q2)
      as Q3.
    apply (eq_cl (λ x, E(R, A)[a2] ∈ x) (fval_i _ _ _ (eps_fn _ _ P1) P3) Q3).
Qed.

Lemma eps_inj: ∀ R, ∀ A, wo R A → inj (E(R, A)) A (EI(R, A)).
Proof.
  intros R A P1.
  split. 
  + apply (eps_fnm _ _ P1).
  + apply (eps_sing_rot _ _ P1).
Qed.

Lemma eps_surj: ∀ R, ∀ A, wo R A → surj (E(R, A)) A (EI(R, A)).
  intros R A P1.
  split. 
  + apply (eps_fnm _ _ P1).
  + apply eq_r. 
Qed.

Lemma eps_bij: ∀ R, ∀ A, wo R A → bij (E(R, A)) A (EI(R, A)).
Proof.
  intros R A P1.
  apply bij_i.
  + apply (eps_surj _ _ P1).
  + apply (eps_inj _ _ P1).
Qed.

Lemma eps_in_e: ∀ R, ∀ A, ∀ x, ∀ y, wo R A → x ∈ A → y ∈ A 
  → (E(R, A))[x] ∈ (E(R, A))[y] → x <[R] y.
Proof.
  intros R A x y P1 P2 P3 P4.
  destruct (eps_e2 _ _ _ _ P1 P3 P4) as [s [P5 [P6 P7]]].
  pose (eq_cr (λ s, x ∈ s) (eps_dom _ _ P1) P2) as Q1.
  pose (eq_cr (λ x, s ∈ x) (eps_dom _ _ P1) P6) as Q2.
  apply (eq_cr (λ x, x <[R] y) (fval_inj _ _ _ _ _ (eps_inj _ _ P1) Q1 Q2 P5)).
  apply P7.
Qed.

Lemma eps_image_i1: ∀ R, ∀ A, ∀ t, wo R A → t ∈ A → E(R, A)[t] ∈ EI(R, A).
Proof.
  intros R A x P1 P2.
  apply ran_i.
  exists x.
  apply fval_e.
  + apply eq_r.
  + apply (eps_fn _ _ P1).
  + apply (eq_cr (λ y, x ∈ y) (eps_dom _ _ P1)).
    apply P2.
Qed.

Lemma eps_image_i2: ∀ R, ∀ A, ∀ t, ∀ s, wo R A → t ∈ A → s ∈ E(R, A)[t]
  → s ∈ EI(R, A).
Proof.
  intros R A x s P1 P2 P3.
  destruct (eps_e2 _ _ _ _ P1 P2 P3) as [y [P4 [P5 P6]]].
  apply (eq_cr (λ s, s ∈ EI(R, A)) P4).
  apply (eps_image_i1 _ _ _ P1 P5).
Qed.

Lemma eps_image_e: ∀ R, ∀ A, ∀ t, wo R A → t ∈ EI(R, A) 
  → ∃ s, s ∈ A ∧ t = E(R, A)[s].
Proof.
  intros R A x P1 P2.
  destruct (ran_e _ _ P2) as [s P3].
  exists s.
  split.
  + apply (eq_cl (λ x, s ∈ x) (eps_dom _ _ P1)).
    apply (dom_i2 _ _ _ P3).
  + apply (fval_i _ _ _ (eps_fn _ _ P1) P3).
Qed.

Lemma eps_image_t: ∀ R, ∀ A, wo R A → trans (EI(R, A)).
Proof.
  intros R A P1 x a P2 P3.
  destruct (eps_image_e _ _ _ P1 P3) as [s [P4 P5]].
  apply (eps_image_i2 _ _ _ _ P1 P4 (eq_cl (λ a, x ∈ a) P5 P2)).
Qed.

Lemma eps_rel_i: ∀ R, ∀ A, ∀ a1, ∀ a2, wo R A → a1 ∈ A → a2 ∈ A → 
  E(R, A)[a1] ∈ E(R, A)[a2] → E(R, A)[a1] <[ER(R, A)] E(R, A)[a2].
Proof.
  intros R A a1 a2 P1 P2 P3 P4.
  apply sub_i.
  + apply cp_i.
    - apply (eps_image_i1 _ _ _ P1 P2).
    - apply (eps_image_i1 _ _ _ P1 P3).
  + exists (E(R, A)[a1]).
    exists (E(R, A)[a2]).
    split.
    - apply eq_r.
    - apply P4.
Qed.
    
Lemma eps_rel_e: ∀ R, ∀ A, ∀ a1, ∀ a2, wo R A → a1 ∈ A → a2 ∈ A →
  E(R, A)[a1] <[ER(R, A)] E(R, A)[a2] → (eps R A)[a1] ∈ (eps R A)[a2].
Proof.
  intros R A a1 a2 P1 P2 P3 P4.
  destruct (sub_e _ _ _ P4) as [_ [x [y [P5 P6]]]].
  apply (eq_cr (λ x, x ∈ E(R, A)[a2]) (opair_eq_el _ _ _ _ P5)).
  apply (eq_cr (λ y, x ∈ y) (opair_eq_er _ _ _ _ P5)).
  apply P6.
Qed.
    
Lemma eps_rel_e2: ∀ R, ∀ A, ∀ s1, ∀ s2, wo R A → s1 <[ER(R, A)] s2
  → (∃ t1, s1 = E(R, A)[t1]) ∧ (∃ t2, s2 = E(R, A)[t2]).
Proof.
  intros R A s1 s2 P1 P2.
  destruct (sub_e _ _ _ P2) as [P3 _].
  destruct (cp_e2 _ _ _ _ P3) as [P4 P5].
  destruct (ran_e _ _ P4) as [t1 P6].
  destruct (ran_e _ _ P5) as [t2 P7].
  split.
  + exists t1.
    apply (fval_i _ _ _ (eps_fn _ _ P1) P6).
  + exists t2.
    apply (fval_i _ _ _ (eps_fn _ _ P1) P7).
Qed.

Lemma eps_rel_less_e: ∀ R, ∀ A, ∀ x, ∀ y, wo R A → x ∈ A → y ∈ A → x <[R] y 
  → E(R, A)[x] <[ER(R, A)] E(R, A)[y].
Proof.
  intros R A x y P1 P2 P3 P4.
  apply (eps_rel_i _ _ _ _ P1 P2 P3).
  apply (eps_in_i _ _ _ _ P1 P2 P3 P4).
Qed.

Lemma eps_rel_less_i: ∀ R, ∀ A, ∀ x, ∀ y, wo R A → x ∈ A → y ∈ A
  → E(R, A)[x] <[ER(R,A)] E(R, A)[y] → x <[R] y.
Proof.
  intros R A x y P1 P2 P3 P4.
  apply (eps_in_e _ _ _ _ P1 P2 P3).
  apply (eps_rel_e _ _ _ _ P1 P2 P3 P4).
Qed.

Lemma eps_image_rel_eq: ∀ R, ∀ A, ∀ S, ∀ B, wo R A → wo S B 
  → EI(R, A) = EI(S, B) → ER(R, A) = ER(S, B).
Proof.
  intros R A S B P1 P2 P3.
  unfold eps_rel.
  apply (eq_cr 
    (λ r, {s: r ⨉ r| ∃ x, ∃ y, s = ⟨x, y⟩ ∧ x ∈ y} 
        = {s: EI(S, B) ⨉ EI(S, B)| ∃ x, ∃ y, s = ⟨x, y⟩ ∧ x ∈ y}) P3).
  apply eq_r.
Qed.
(*----------------------------------------------------------------------------*)
  
(* More WO *)
Lemma wo_seg: ∀ R, ∀ A, ∀ t, wo R A → t ∈ A → wo R (seg R A t).
Proof.
  intros R A x P1 P2.
  apply (sub_wo _ _ _ P1).
  apply sub_e1.
Qed.

Lemma wo_eps_isom: ∀ R, ∀ A, wo R A → isom R A (ER(R, A)) (EI(R, A)).
Proof.
  intros R A P1.
  exists (eps R A).
  split.
  + apply (eps_bij _ _ P1).
  + split.
    - intros x y P2 P3 P4.
      apply (eps_rel_less_e _ _ _ _ P1 P2 P3 P4).
    - intros x y P2 P3 P4.
      apply (eps_rel_less_i _ _ _ _ P1 P2 P3 P4).
Qed.

Lemma wo_eps_eq_isom: ∀ R, ∀ A, ∀ S, ∀ B, wo R A → wo S B → 
  EI(R, A) = EI(S, B) → isom R A S B.
Proof.
  intros R A S B P1 P2 P3.
  pose (wo_eps_isom _ _ P1) as Q1.
  pose (isom_s _ _ _ _ (wo_eps_isom _ _ P2)) as Q2.
  pose (eq_cl (λ x, isom R A (ER(R, A)) x) P3 Q1) as Q3.
  pose (eq_cl (λ x, isom R A x (EI(S, B))) (eps_image_rel_eq _ _ _ _ P1 P2 P3) Q3) as Q4.
  apply (isom_t _ _ _ _ _ _ Q4 Q2).
Qed.

Lemma wo_isom_eps_eq: ∀ R, ∀ A, ∀ S, ∀ B, wo R A → wo S B → 
  isom R A S B → (EI(R, A)) = (EI(S, B)).
Proof.
  intros R A S B P1 P2 [f [P3 [P4 P5]]].
  pose ({x: A| E(R, A)[x] = E(S, B)[f[x]]}) as C.
  pose (sub_e1 (λ x, E(R, A)[x] = E(S, B)[f[x]]) A) as I1.
  assert (∀ s, s ∈ A → seg R A s ⊆ C → s ∈ C) as I2.
  { intros s Q1 Q2.
    apply sub_i.
    + apply Q1.
    + assert (f[s] ∈ B) as Q3.
      { destruct P3 as [[P6 [P7 _]] [P8 _]].
        apply (eq_cl (λ x, f[s] ∈ x) P8).
        apply (fval_ran _ _ P6).
        apply (eq_cr (λ x, s ∈ x) P7).
        apply Q1. }
      apply (eq_cr (λ x, x = E(S, B)[f[s]]) (eps_e1 _ _ _ P1 Q1)).
      apply (eq_cr (λ x, E(R, A)⟦seg R A s⟧ = x) (eps_e1 _ _ _ P2 Q3)).
      apply sub_a.
      split.
      - intros y R1.
        destruct P3 as [[S1 [S2 _]] [S3 _]].
        destruct (seg_image_e _ _ _ _ _ Q1 R1) as [x [R2 [R3 [R4 R5]]]].
        apply (seg_image_i _ _ _ _ (f[x]) ).
        * apply (eq_cl (λ y, f[x] ∈ y) S3).
          apply (fval_ran _ _ S1).
          apply (eq_cr (λ y, x ∈ y) S2 R3).
        * apply (eq_cr (λ y, ⟨f[x] ,y⟩ ∈ E(S, B))
            (fval_i _ _ _ (eps_fn _ _ P1) R4)).
          destruct (sub_e _ _ _ (Q2 _ (seg_i _ _ _ _ R3 R5))) as [_ R6].
          apply (eq_cr (λ y, ⟨f[x] ,y⟩ ∈ E(S, B)) R6).
          apply fval_i2.
          ++apply (eps_fn _ _ P2).
          ++apply (eq_cr (λ y, f[x] ∈ y) (eps_dom _ _ P2)).
            apply (eq_cl (λ y, f[x] ∈ y) S3).
            apply (fval_ran _ _ S1).
            apply (eq_cr (λ y, x ∈ y) S2 R3).
        * apply (P4 _ _ R3 Q1 R5).
      - intros x R1.
        assert (inj f A B) as S0.
        { apply (bij_e _ _ _ P3). }
        destruct P3 as [[S1 [S2 _]] [S3 S4]].
        destruct (inv_fn f) as [S5 _].
        pose (S5 S4) as S11.
        pose (eq_cr (λ x, x = B) (inv_dom _) S3) as S12.
        pose (eq_cr (λ x, x = A) (inv_ran _) S2) as S13.
        pose (inv_sing_val f (and_er S1)) as S14.
        destruct (seg_image_e _ _ _ _ _ Q3 R1) as [y [R2 [R3 [R4 R5]]]].
        assert ((inv f)[y] <[R] s) as R15.
        { apply P5.
          + apply (eq_cl (λ x, (inv f)[y] ∈ x) S13).
            apply (fval_ran _ _ S11).
            apply (eq_cr (λ x, y ∈ x) S12 R3).
          + apply Q1.
          + apply (eq_cr (λ y, y <[S] f[s])
              (inv_fn_ex2 _ _ _ _ S0 (eq_cr (λ x, y ∈ x) S3 R3))).
            apply R5. }
        assert ((inv f)[y] ∈ A) as R13.
        { apply (eq_cl (λ x, (inv f)[y] ∈ x) S13).
          apply (fval_ran _ _ S11).
          apply (eq_cr (λ x, y ∈ x) S12 R3). }
        apply (seg_image_i _ _ _ _ ((inv f)[y])).
        * apply (eq_cl (λ x, (inv f)[y] ∈ x) S2).
          apply (eq_cl (λ x, (inv f)[y] ∈ x) (inv_ran _)).
          apply (fval_ran _ _ S11).
          apply (eq_cr (λ x, y ∈ x) S12 R3).
        * apply (eq_cr (λ x, ⟨(inv f)[y] ,x⟩ ∈ E(R, A))
            (fval_i _ _ _ (eps_fn _ _ P2) R4)).
          destruct (sub_e _ _ _ (Q2 _ (seg_i _ _ _ _ R13 R15))) as [_ R6].
          apply (eq_cl (λ s, ⟨(inv f)[y], E(S, B)[s]⟩ ∈ E(R, A))
            (inv_fn_ex2 _ _ _ _ S0 (eq_cr (λ x, y ∈ x) S3 R3))).
          apply (eq_cl (λ x, ⟨(inv f)[y] ,x⟩ ∈ E(R, A)) R6).
          apply fval_i2.
          ++apply (eps_fn _ _ P1).
          ++apply (eq_cr (λ x, (inv f)[y] ∈ x) (eps_dom _ _ P1)).
            apply (eq_cl (λ x, (inv f)[y] ∈ x) S13).
            apply (fval_ran _ _ S11).
            apply (eq_cr (λ x, y ∈ x) S12 R3).
        * apply R15. }
  pose (transfinite_induction _ _ _ P1 (and_i I1 I2)) as I3.
  apply sub_a.
  split.
  + intros x Q1.
    destruct (eps_image_e _ _ _ P1 Q1) as [s [Q2 Q3]].
    apply (eq_cr (λ x, x ∈ EI(S, B)) Q3).
    destruct (sub_e _ _ _ (eq_cl (λ y, s ∈ y) I3 Q2)) as [_ Q4].
    apply (eq_cr (λ x, x ∈ EI(S, B)) Q4).
    apply (eps_image_i1 _ _ _ P2).
    destruct P3 as [[S1 [S2 _]] [S3 _]].
    apply (eq_cl (λ x, f[s] ∈ x) S3).
    apply (fval_ran _ _ S1).
    apply (eq_cr (λ x, s ∈ x) S2).
    apply (I1 _ (eq_cl (λ y, s ∈ y) I3 Q2)).
  + intros x Q1.
    destruct (eps_image_e _ _ _ P2 Q1) as [s [Q2 Q3]].
    assert ((inv f)[s] ∈ A) as Q4.
    { destruct P3 as [[S1 [S2 _]] [S3 S4]].
      apply (eq_cl (λ x, (inv f)[s] ∈ x) S2).
      apply (eq_cl (λ x, (inv f)[s] ∈ x) (inv_ran _)).
      apply fval_ran.
      * apply inv_fn.
        apply S4.
      * apply (eq_cr (λ x, s ∈ x) (inv_dom _)).
        apply (eq_cr (λ x, s ∈ x) S3).
        apply Q2. }
    assert (inj f A B) as S0.
    { apply (bij_e _ _ _ P3). }
    destruct P3 as [[S1 [S2 _]] [S3 S4]].
    pose (eq_cr _ S3 Q2) as Q22.
    (*rewrite <- P6 in Q2.*)
    pose (eq_cr (λ s, x = E(S, B)[s]) (inv_fn_ex2 _ _ _ _ S0 Q22) Q3) as Q33.
    (*rewrite <- (inv_function_exist_2 _ P3 _ Q2) in Q3.*)
    pose (eq_cl _ I3 Q4) as Q44.
    (*rewrite I3 in Q4.*)
    destruct (sub_e _ _ _ Q44) as [_ Q5].
    apply (eq_cr (λ x, x ∈ EI(R, A)) Q33).
    apply (eq_cl (λ x, x ∈ EI(R, A)) Q5).
    apply (eps_image_i1 _ _ _ P1).
    apply (I1 _ Q44).
Qed.

(* Ordinal Number *)
Definition Ord (x: J) := ∃ R, ∃ A, wo R A ∧ x = EI(R, A).

Lemma ord_i: ∀ R, ∀ A, wo R A → ∃ x, Ord x.
Proof.
  intros R A P1.
  exists (eps_image R A).
  exists R.
  exists A.
  split.
  + apply P1.
  + apply eq_r.
Qed.

