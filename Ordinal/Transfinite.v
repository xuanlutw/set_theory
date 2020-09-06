Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Nat.
Require Import Ordinal.Order.
 
(*Require dpdgraph.dpdgraph.*)

(* Initial Segment *)
Definition seg (R A a: J) := {x: A| x <[R] a}.
Definition l_ind (R A B: J) := B ⊆ A ∧ ∀ t, t ∈ A → seg R A t ⊆ B → t ∈ B.

Lemma seg_i: ∀ R, ∀ A, ∀ x, ∀ y, y ∈ A → y <[R] x → y ∈ (seg R A x).
Proof.
  intros R A x y P1 P2.
  apply sub_i.
  + apply P1.
  + apply P2.
Qed.

Lemma seg_e1: ∀ R, ∀ A, ∀ x, ∀ y, x ∈ A → y ∈ (seg R A x) → y ∈ A.
Proof.
  intros R A x y P1 P2.
  destruct (sub_e _ _ _ P2) as [P3 _].
  apply P3.
Qed.

Lemma seg_e2: ∀ R, ∀ A, ∀ x, ∀ y, x ∈ A → y ∈ (seg R A x) → y <[R] x.
Proof.
  intros R A x y P1 P2.
  destruct (sub_e _ _ _ P2) as [P3 P4].
  apply P4.
Qed.

Lemma seg_sub: ∀ R, ∀ A, ∀ t, t ∈ A → seg R A t ⊆ A.
Proof.
  intros R A t P1 x P2.
  apply (seg_e1 _ _ _ _ P1 P2).
Qed.

Lemma seg_seg: ∀ R, ∀ A, ∀ t1, ∀ t2, r_trans R A → t1 ∈ A → t2 ∈ A → t1 <[R] t2 
  → seg R A t1 = seg R (seg R A t2) t1.
Proof.
  intros R A t1 t2 P0 P1 P2 P3.
  apply sub_a.
  split.
  + intros x P4.
    pose (seg_e1 _ _ _ _ P1 P4) as P5.
    pose (seg_e2 _ _ _ _ P1 P4) as P6.
    apply seg_i.
    - apply seg_i.
      * apply P5.
      * apply (l_l_t _ _ _ _ _ P0 P5 P1 P2 P6 P3).
    - apply P6.
  + intros x P4.
    pose (seg_i _ _ _ _ P1 P3) as P5.
    pose (seg_e1 _ _ _ _ P5 P4) as P6.
    pose (seg_e2 _ _ _ _ P5 P4) as P7.
    apply seg_i.
    - apply (seg_e1 _ _ _ _ P2 P6).
    - apply P7.
Qed.
    
Lemma seg_less_sub: ∀ R, ∀ A, ∀ t1, ∀ t2, r_trans R A → t1 ∈ A → t2 ∈ A
  → t1 <[R] t2 → seg R A t1 ⊆ seg R A t2.
Proof.
  intros R A t1 t2 P1 P2 P3 P4 s P5.
  pose (seg_e1 _ _ _ _ P2 P5) as P6.
  pose (seg_e2 _ _ _ _ P2 P5) as P7.
  apply seg_i.
  + apply P6.
  + apply (l_l_t _ _ _ _ _ P1 P6 P2 P3 P7 P4).
Qed.

Lemma seg_image_e: ∀ R, ∀ A, ∀ f, ∀ t, ∀ y, t ∈ A → y ∈ f⟦seg R A t⟧ 
  → ∃ x, x ∈ dom(f) ∧ x ∈ A ∧ ⟨x, y⟩ ∈ f ∧ x <[R] t.
Proof.
  intros R A f t y P1 P2.
  destruct (image_e _ _ _ P2) as [x [Q1 Q2]].
  pose (seg_e1 _ _ _ _ P1 Q2) as Q3.
  pose (seg_e2 _ _ _ _ P1 Q2) as Q4.
  exists x.
  repeat split.
  + apply (dom_i2 _ _ _ Q1).
  + apply Q3.
  + apply Q1.
  + apply Q4.
Qed.

Lemma seg_image_i: ∀ R, ∀ A, ∀ f, ∀ t, ∀ x, ∀ y, x ∈ A → ⟨x, y⟩ ∈ f → x <[R] t
  → y ∈ f⟦seg R A t⟧ .
Proof.
  intros R A f t x y P1 P2 P3.
  apply image_i.
  exists x.
  split.
  + apply P2.
  + apply seg_i.
    - apply P1.
    - apply P3.
Qed.

Lemma wo_prop_seg: ∀ₚ P, ∀ R, ∀ A, ∀ x0, wo R A → x0 ∈ A → P x0
  → ∃ x, x ∈ A ∧ P x ∧ (∀ y, y ∈ seg R A x → ~ P y).
Proof.
  intros P R A x0 P1 P2 P3.
  destruct (wo_prop_least _ _ _ _ P1 P2 P3) as [x [Q1 [Q2 Q3]]].
  exists x.
  repeat split.
  + apply Q1.
  + apply Q2.
  + intros y Q4 Q5.
    pose (seg_e1 _ _ _ _ Q1 Q4) as Q6.
    apply (wo_nle_i _ _ _ _ P1 Q6 Q1 (seg_e2 _ _ _ _ Q1 Q4)).
    apply (Q3 _ Q6 Q5).
Qed.

Lemma wo_seg: ∀ R, ∀ A, ∀ t, wo R A → t ∈ A → wo R (seg R A t).
Proof.
  intros R A x P1 P2.
  apply (sub_wo _ _ _ P1).
  apply sub_e1.
Qed.
(*----------------------------------------------------------------------------*)

(* Transfinite *)
Theorem transfinite_induction: ∀ R, ∀ A, ∀ B, wo R A → l_ind R A B →
  A = B.
Proof.
  intros R A B P1 [P2 P3].
  destruct (sub_e2 _ _ P2) as [P4 | P4].
  + destruct ((wo_least_prop _ _ P1) (A \ B) (compl_sub A B) 
      (compl_psub_nempty _ _ P4)) as [x [P5 P6]].
    destruct (compl_e _ _ _ P5) as [P7 P8].
    apply bot_e.
    apply P8.
    apply (P3 _ P7).
    intros y P9.
    pose (seg_e1 _ _ _ _ P7 P9) as P10.
    destruct (compl_dilemma _ B _ P10) as [P11 | P11].
    - destruct (inter2_e _ _ _ P11) as [_ P12].
      apply P12.
    - apply bot_e.
      apply (wo_nl_i _ _ _ _ P1 P7 P10 (P6 _ P11)).
      apply (seg_e2 _ _ _ _ P7 P9).
  + apply (eq_s P4).
Qed.
(* Skip 7C *)

Definition _G_unique (G: J → J → Prop) := 
  (∀ x, ∃ y, G x y) ∧ (∀ x, ∀ y1, ∀ y2, G x y1 → G x y2 → y1 = y2).
Definition _G_constr (G: J → J → Prop) (R A f t: J) :=
  t ∈ A ∧ fn f ∧ dom(f) = {x: A| x ≤[R] t} ∧
  ∀ x, x ∈ dom(f) → G (f ↾ (seg R A x)) (f[x]).

Lemma _G_constr_consist: ∀ₚₚ G, ∀ R, ∀ A, ∀ f1, ∀ f2, ∀ t1, ∀ t2,
  wo R A → _G_unique G 
  → _G_constr G R A f1 t1 → _G_constr G R A f2 t2 → t1 ≤[R] t2 
  → ∀ x, x ∈ A → x ≤[R] t1 → f1[x] = f2[x].
Proof.
  intros G R A f1 f2 t1 t2 P1 [_ P2] [P3 [P4 [P5 P6]]] [P7 [P8 [P9 P10]]] P11.
  apply nn_e.
  intros Q1.
  destruct (not_all_ex_not _ Q1) as [x Q2].
  destruct (nimp_e Q2) as [Q3 Q4].
  destruct (nimp_e Q4) as [Q5 Q6].
  destruct (wo_prop_least (λ x, x ≤[R] t1 ∧ f1[x] ≠ f2[x]) _ _ _ P1 Q3 
    (and_i Q5 Q6)) as [x0 [R1 [[R2 R3] R4]]].
  assert (f1 ↾ seg R A x0 = f2 ↾ seg R A x0) as R5.
  { apply sub_a.
    split.
    + intros s S1.
      destruct (restr_e2 _ _ _ S1) as [sx [sy [S2 [S3 S4]]]].
      pose (seg_e2 _ _ _ _ R1 S4) as S5.
      pose (seg_e1 _ _ _ _ R1 S4) as S6.
      pose (contraposition1 (R4 _ S6)) as S7.
      destruct (not_and_or (S7 (wo_nle_i _ _ _ _ P1 S6 R1 S5))) as [S8 | S8].
      - apply bot_e.
        apply S8.
        left.
        apply (l_le_t _ _ _ _ _ (wo_trans _ _ P1) S6 R1 P3 S5 R2).
      - apply (eq_cr (λ s, s ∈ f2↾(seg R A x0)) S3).
        apply restr_i.
        * apply fval_e.
          ++apply (eq_cl (λ x, sy = x) (nn_e S8)).
            apply (fval_i _ _ _ P4 S2).
          ++apply P8.
          ++apply (eq_cr (λ x, sx ∈ x) P9).
            apply sub_i.
            --apply S6.
            --left.
              apply (l_le_t _ _ _ _ _ (wo_trans _ _ P1) S6 P3 P7
                (l_le_t _ _ _ _ _ (wo_trans _ _ P1) S6 R1 P3 S5 R2) P11).
        * apply S4.
    + intros s S1.
      destruct (restr_e2 _ _ _ S1) as [sx [sy [S2 [S3 S4]]]].
      pose (seg_e2 _ _ _ _ R1 S4) as S5.
      pose (seg_e1 _ _ _ _ R1 S4) as S6.
      pose (contraposition1 (R4 _ S6)) as S7.
      destruct (not_and_or (S7 (wo_nle_i _ _ _ _ P1 S6 R1 S5))) as [S8 | S8].
      - apply bot_e.
        apply S8.
        left.
        apply (l_le_t _ _ _ _ _ (wo_trans _ _ P1) S6 R1 P3 S5 R2).
      - apply (eq_cr (λ s, s ∈ f1↾(seg R A x0)) S3).
        apply restr_i.
        * apply fval_e.
          ++apply (eq_cr (λ x, sy = x) (nn_e S8)).
            apply (fval_i _ _ _ P8 S2).
          ++apply P4.
          ++apply (eq_cr (λ x, sx ∈ x) P5).
            apply sub_i.
            --apply S6.
            --left.
              apply (l_le_t _ _ _ _ _ (wo_trans _ _ P1) S6 R1 P3 S5 R2).
        * apply S4. }
  apply R3.
  apply (P2 (f1 ↾ (seg R A x0))).
  + apply P6.
    apply (eq_cr _ P5).
    apply sub_i.
    - apply R1.
    - apply R2.
  + apply (eq_cr (λ x, G (x) (f2[x0])) R5).
    apply P10.
    apply (eq_cr _ P9).
    apply sub_i.
    - apply R1.
    - apply (le_le_t _ _ _ _ _ (wo_trans _ _ P1) R1 P3 P7 R2 P11).
Qed.

Theorem transfinite_recursion: ∀ₚₚ G, ∀ R, ∀ A, wo R A → _G_unique G
  → ∃ F, fn F ∧ dom(F) = A ∧ (∀ t, t ∈ A → G (F↾ (seg R A t)) (F[t])).
Proof.
  intros G R A P1 P2.
  pose (λ t, λ f, fn f ∧ _G_constr G R A f t) as G'.
  assert (∀ x, ∀ y1, ∀ y2, x ∈ A → G' x y1 → G' x y2 → y1 = y2) as P3.
  { intros t f1 f2 S1 [S2 S3] [S4 S5].
    apply fn_eq.
    + apply S2.
    + apply S4.
    + destruct S3 as [_ [_ [S3 _]]].
      apply (eq_cr (λ x, x = dom(f2)) S3).
      destruct S5 as [_ [_ [S5 _]]].
      apply (eq_s S5).
    + intros x S6.
      apply (_G_constr_consist _ _ _ _ _ _ _ P1 P2 S3 S5).
      - right.
        apply eq_r.
      - destruct S3 as [_ [_ [S3 _]]].
        destruct (sub_e _ _ _ (eq_cl (λ y, x ∈ y) S3 S6)) as [S7 _].
        apply S7.
      - destruct S3 as [_ [_ [S3 _]]].
        destruct (sub_e _ _ _ (eq_cl (λ y, x ∈ y) S3 S6)) as [_ S7].
        apply S7. }
  destruct (ax_replace _ _ P3) as [H P4].
  assert (rel (∪H)) as P5.
  { apply union_rel.
    intros f Q1.
    destruct (P4 f) as [Q2 _].
    destruct (Q2 Q1) as [t [_ [[Q3 _] _]]].
    apply Q3. }
  assert (sing_val (∪H)) as P6.
  { intros x y1 y2 Q1 R1.
    destruct (union_e _ _ Q1) as [fQ [Q3 Q4]].
    destruct (P4 fQ) as [Q5 _].
    destruct (Q5 Q3) as [tQ [Q6 [Q7 Q8]]].
    assert (dom(fQ) = {x: A |x ≤[R] tQ}) as Q9.
    { destruct Q8 as [_ [_ [Q8 _]]].
      apply Q8. }
    pose (eq_cl (λ y, x ∈ y) Q9 (dom_i2 _ _ _ Q4)) as Q10.
    destruct (sub_e _ _ _ Q10) as [Q11 Q12].
    apply (eq_cr (λ x, x = y2) (fval_i _ _ _ Q7 Q4)).
    destruct (union_e _ _ R1) as [fR [R3 R4]].
    destruct (P4 fR) as [R5 _].
    destruct (R5 R3) as [tR [R6 [R7 R8]]].
    assert (dom(fR) = {x: A |x ≤[R] tR}) as R9.
    { destruct R8 as [_ [_ [R8 _]]].
      apply R8. }
    pose (eq_cl (λ y, x ∈ y) R9 (dom_i2 _ _ _ R4)) as R10.
    destruct (sub_e _ _ _ R10) as [R11 R12].
    apply (eq_cr (λ y, fQ[x] = y) (fval_i _ _ _ R7 R4)).
    destruct (wo_tricho_weak _ _ P1 _ _ Q6 R6) as [P6 | [P6 | P6]].
    - apply (_G_constr_consist _ _ _ _ _ _ _ P1 P2 Q8 R8 
        (or_il _ P6) _ Q11 Q12).
    - apply (_G_constr_consist _ _ _ _ _ _ _ P1 P2 Q8 R8 
        (or_ir _ P6) _ Q11 Q12).
    - apply eq_s.
      apply (_G_constr_consist _ _ _ _ _ _ _ P1 P2 R8 Q8 
        (or_il _ P6) _ R11 R12). }
  assert (dom(∪H) = A) as P7.
  { apply nn_e.
    intros P7.
    destruct (neq_e _ _ P7) as [x [[Q1 Q2] | [Q1 Q2]]].
    - apply Q2.
      destruct (dom_e _ _ Q1) as [y Q3].
      destruct (union_e _ _ Q3) as [f [Q4 Q5]].
      destruct (P4 f) as [Q6 _].
      destruct (Q6 Q4) as [t [_ [_ [_ [_ [Q7 _]]]]]].
      pose (eq_cl (λ y, x ∈ y) Q7 (dom_i2 _ _ _ Q5)) as Q8.
      destruct (sub_e _ _ _ Q8) as [Q9 _].
      apply Q9.
    - destruct (wo_prop_least (λ x, x ∉ dom(∪H)) _ _ _ P1 Q1 Q2) 
        as [x0 [Q3 [Q4 Q5]]].
      assert (dom(∪H) = seg R A x0) as Q6.
      { apply sub_a.
        split.
        + intros xx R1.
          destruct (dom_e _ _ R1) as [yy R2].
          destruct (union_e _ _ R2) as [f [R4 R5]].
          destruct (P4 f) as [R6 _].
          destruct (R6 R4) as [t [S1 [_ [_ [_ [R7 _]]]]]].
          pose (eq_cl (λ y, xx ∈ y) R7 (dom_i2 _ _ _ R5)) as R8.
          destruct (sub_e _ _ _ R8) as [R9 R10].
          apply seg_i.
          - apply R9.
          - destruct (wo_tricho_weak _ _ P1 _ _ R9 Q3) as [R11 | [R11 | R11]].
            * apply R11.
            * apply bot_e.
              apply Q4.
              apply (eq_cl (λ x, x ∈ dom(∪H)) R11 R1).
            * pose (l_le_t _ _ _ _ _ (wo_trans _ _ P1) Q3 R9 S1 R11 R10) as R12. 
              pose (sub_i (λ x, x ≤[R] t) _ _ Q3 (or_il _ R12)) as R13.
              pose (eq_cr (λ y, x0 ∈ y) R7 R13) as R14.
              apply bot_e.
              apply Q4.
              apply (union_dom_i _ _ _ R14 R4).
        + intros xx R1.
          pose (seg_e1 _ _ _ _ Q3 R1) as R2.
          pose (seg_e2 _ _ _ _ Q3 R1) as R3.
          apply nn_e.
          apply (contraposition1 (Q5 _ R2)).
          apply (wo_nle_i _ _ _ _ P1 R2 Q3 R3). }
      destruct P2 as [R1 R2].
      destruct (R1 (∪H)) as [y R3].
      assert (fn ((∪H) ∪ J{⟨x0, y⟩})) as Q7.
      { split.
        + apply (rel_exten _ _ _ P5).
        + apply (sing_val_exten _ _ _ P6 Q4). }
      assert ((∪H) ∪ J{⟨x0, y⟩} ∈ H) as R4.
      { assert (dom(∪H ∪ J{⟨x0, y⟩}) = {x1: A | x1 ≤[R] x0}) as R4.
        { apply (eq_cr (λ x, x = {y: A| y ≤[R] x0}) (union2_dom _ _)).
          apply (eq_cr (λ x, dom(∪H) ∪ dom(J{⟨x0, y⟩}) = x) 
            (sub_exten _ _ _ Q3)).
          apply (eq_cr (λ x, x ∪ dom(J{⟨x0, y⟩}) = {x1: A | x1 <[R] x0} ∪ J{x0})
              Q6).
          apply (eq_cr (λ x, (seg R A x0) ∪ x = {x1 : A | x1 <[ R] x0} ∪ J{ x0})
              (sing_pair_dom _ _)).
          apply eq_r. }
        apply P4.
        exists x0.
        repeat split.
        + apply Q3.
        + apply (rel_exten _ _ _ P5).
        + apply (sing_val_exten _ _ _ P6 Q4).
        + apply Q3.
        + apply (rel_exten _ _ _ P5).
        + apply (sing_val_exten _ _ _ P6 Q4).
        + apply R4.
        + intros xx S1.
          pose (eq_cl (λ x, xx ∈ x) (union2_dom _ _ ) S1) as S2.
          destruct (union2_e _ _ _ S2) as [S3 | S3].
          - destruct (union_dom_e _ _ S3) as [f [S4 S5]].
            destruct (P4 f) as [S6 _].
            destruct (S6 S5) as [t [_ [_ [S7 [S8 [S9 S10]]]]]].
            assert ((∪H ∪ J{⟨x0, y⟩})[xx] = f[xx]) as S11.
            { pose (union2_fvall _ _ _ (and_i P5 P6) Q7 S3) as T1.
              pose (union_fval _ _ _ S5 S8 (and_i P5 P6) S4) as T2.
              apply (eq_cl (λ x, x = f[xx]) T1).
              apply (eq_s T2). }
            assert ((∪H ∪ J{⟨x0, y⟩})↾(seg R A xx) = f↾(seg R A xx)) as S12.
            { apply eq_s.
              apply (sub_restr_eq _ _ _ S8 Q7).
              + apply union2_sub_weak_l.
                apply (union_i2 _ _ S5).
              + intros s T1.
                destruct (sub_e _ _ _ (eq_cl (λ x, xx ∈ x) S9 S4)) as [T2 T3].
                pose (seg_e1 _ _ _ _ T2 T1) as T4.
                pose (seg_e2 _ _ _ _ T2 T1) as T5.
                apply (eq_cr (λ y, s ∈ y) S9).
                apply sub_i.
                - apply T4.
                - left.
                  apply (l_le_t _ _ _ _ _ (wo_trans _ _ P1) T4 T2 S7 T5 T3). }
            apply (eq_cr (λ x, G x ((∪H ∪ J{⟨x0, y⟩})[xx])) S12).
            apply (eq_cr (λ x, G (f↾(seg R A xx)) x) S11).
            apply S10.
            apply S4.
          - pose (sing_e _ _ (eq_cl (λ x, xx ∈ x) (sing_pair_dom _ _) S3)) as S4.
            assert ((∪H ∪ J{⟨x0, y⟩})[xx] = y) as S5.
            { pose (union2_fvalr _ _ _ (sing_pair_is_fn _ _) Q7 S3) as T1.
              apply (eq_cl (λ x, x = y) T1).
              apply (eq_cl (λ x, J{⟨x0, y⟩}[x] = y) S4).
              apply (eq_cr (λ x, x = y) (sing_pair_fval _ _)).
              apply eq_r. }
            assert ((∪H ∪ J{⟨x0, y⟩})↾(seg R A xx) = ∪H) as S6.
            { apply (@eq_t _ ((∪H)↾ seg R A xx)).
              + apply eq_s.
                apply (sub_restr_eq _ _ _ (and_i P5 P6) Q7).
                - apply union2_sub_weak_l.
                  apply sub_r.
                - intros s T1.
                  pose (eq_cl (λ x, x ∈ A) S4 Q3) as T2.
                  pose (seg_e1 _ _ _ _ T2 T1) as T4.
                  pose (seg_e2 _ _ _ _ T2 T1) as T5.
                  apply (eq_cr (λ y, s ∈ y) Q6).
                  apply seg_i.
                  * apply T4.
                  * apply (eq_cr (λ x, s <[R] x) S4).
                    apply T5.
              + apply (restr_over _ _ P5).
                apply (eq_cr (λ x, x ⊆ seg R A xx) Q6).
                apply (eq_cr (λ x, seg R A x ⊆ seg R A xx) S4).
                apply sub_r. }
            apply (eq_cr (λ x, G x ((∪H ∪ J{⟨x0, y⟩})[xx])) S6).
            apply (eq_cr (λ x, G (∪H) x) S5).
            apply R3. }
      apply Q4.
      apply (union_dom_i _ (∪H ∪ J{⟨x0, y⟩})).
      * apply (eq_cr (λ x, x0 ∈ x) (union2_dom _ _)).
        apply union2_ir.
        apply (eq_cr (λ x, x0 ∈ x) (sing_pair_dom _ _)).
        apply sing_i.
      * apply R4. }
  exists (∪H).
  repeat split.
  + apply P5.
  + apply P6.
  + apply P7.
  + intros t Q1.
    destruct (union_dom_e _ _ (eq_cr (λ x, t ∈ x) P7 Q1))
      as [f [Q2 Q3]].
    destruct (P4 f) as [Q4 _].
    destruct (Q4 Q3) as [t' [_ [_ [Q6 [Q7 [Q8 Q9]]]]]].
    pose (union_fval _ _ _ Q3 Q7 (and_i P5 P6) Q2) as Q10.
    assert ((∪H)↾(seg R A t) = f↾(seg R A t)) as Q11.
    { apply eq_s.
      apply (sub_restr_eq _ _ _ Q7 (and_i P5 P6) (union_i2 _ _ Q3)).
      intros x R1.
      pose (seg_e1 _ _ _ _ Q1 R1) as R2.
      pose (seg_e2 _ _ _ _ Q1 R1) as R3.
      destruct (sub_e _ _ _ (eq_cl (λ x, t ∈ x) Q8 Q2)) as [_ R4].
      apply (eq_cr (λ y, x ∈ y) Q8).
      apply sub_i.
      + apply R2.
      + left.
        apply (l_le_t _ _ _ _ _ (wo_trans _ _ P1) R2 Q1 Q6 R3 R4). }
    apply (eq_cr (λ x, G x ((∪H)[t])) Q11).
    apply (eq_cl (λ x, G (f↾(seg R A t)) x) Q10).
    apply Q9.
    apply Q2.
Qed.
(* Skip unique *)
(*----------------------------------------------------------------------------*)
