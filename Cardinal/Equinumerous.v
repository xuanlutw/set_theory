Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Nat.
Require Import Ordinal.Ordinal.

(* Equinumerous *)
Definition eqnum  (A B: J) := ∃ F, bij F A B.
Notation   "A ≈ B"         := (eqnum A B).
Definition neqnum (A B: J) := (~(A ≈ B)).
Notation   "A ≉ B"         := (neqnum A B).

Lemma eqnum_r: ∀ A, A ≈ A.
Proof.
  intros A.
  exists (id A).
  + apply id_is_bij.
Qed.

Lemma eqnum_s: ∀ A, ∀ B, A ≈ B → B ≈ A.
Proof.
  intros A B [F P1].
  exists (inv F).
  apply (inv_bij _ _ _ P1).
Qed.

Lemma eqnum_t: ∀ A, ∀ B, ∀ C, A ≈ B → B ≈ C → A ≈ C.
Proof.
  intros A B C [f P1] [g P2].
  exists (g ∘ f).
  apply (comp_bij _ _ _ _ _ P1 P2).
Qed.

Lemma diagonal: ∀ A, ~(A ≈ 𝒫(A)).
Proof.
  intros A [f [[P1 [P3 _]] [P2 _]]].
  pose ({x: A| x ∉ f[x]}) as B.
  assert (B ∉ ran(f)) as P4.
  { intros Q1.
    destruct (ran_e _ _ Q1) as [x Q2].
    pose (fval_i _ _ _ P1 Q2) as Q3.
    destruct (LEM (x ∈ f[x])) as [Q4 | Q4].
    + pose (eq_cr (λ y, x ∈ y) Q3 Q4) as Q5.
      destruct (sub_e _ _ _ Q5) as [_ Q6].
      apply (Q6 Q4).
    + apply (eq_cr (λ y, x ∉ y) Q3 Q4).
      apply sub_i.
      * apply (eq_cl (λ y, x ∈ y) P3).
        apply (dom_i2 _ _ _ Q2).
      * apply Q4. }
  apply P4.
  apply (eq_cr (λ y, B ∈ y) P2).
  apply power_i.
  apply sub_e1.
Qed.

Definition finite   (A: J) := ∃ n, n ∈ ω ∧ A ≈ n.
Definition infinite (A: J) := ~(finite A).

Lemma pigenhole: ∀ n, ∀ m, n ∈ ω → m ⊂ n → n ≉ m.
Proof.
  intros n m P1 P2 P3.
  pose (λ x, ∀ f, inj f x x → ran(f) = x) as P.
  assert (P 〇ₙ) as I1.
  { intros f [[_ [_ Q1]] _].
    apply (sub_empty_empty _ Q1). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 f Q3.
    assert (fn f) as S1.
    { destruct Q3 as [[Q3 _] _].
      apply Q3. }
    assert (dom(f) = S(k)) as S2.
    { destruct Q3 as [[_ [Q3 _]] _].
      apply Q3. }
    assert (∀ f, inj f (S(k)) (S(k)) → f[k] = k → ran(f) = S(k)) as S3.
    { intros f0 R1 R2.
      assert (fn f0) as R3.
      { destruct R1 as [[R1 _] _].
        apply R1. }
      assert (dom(f0) = S(k)) as R4.
      { destruct R1 as [[_ [R1 _]] _].
        apply R1. }
      pose (f0 \ J{⟨k, f0[k]⟩}) as f1.
      pose (inj_kick _ _ _ _ R1 (suc_i1 k)) as Q5.
      pose (eq_cl (λ s, inj f1 ((S(k)) \ J{k}) ((S(k)) \ J{s})) R2 Q5) as Q6.
      pose (eq_cl (λ s, inj f1 s s) (suc_kick_self k) Q6) as Q7.
      pose (sing_sub_i _ _
        (fval_i2 _ _ R3 (eq_cr (λ x, k ∈ x) R4 (suc_i1 k)))) as Q8.
      apply (eq_cl (λ s, ran(s) = S(k)) (compl_union2_annihilate _ _ Q8)).
      apply (eq_cr (λ s, s = S(k)) (union2_ran _ _)).
      apply (eq_cr (λ s, s ∪ ran(J{⟨k, f0[k]⟩}) = S(k)) (Q2 _ Q7)).
      apply (eq_cr (λ s, k ∪ s = S(k)) (sing_pair_ran _ _)).
      apply (eq_cr (λ s, k ∪ J{s} = S(k)) R2).
      apply eq_r. }
    assert (ran(f) ⊆ S(k)) as S4.
    { destruct Q3 as [[_ [_ Q3]] _].
      apply Q3. }
    assert (sing_rot f) as S5.
    { destruct Q3 as [_ Q3].
      apply Q3. }
    destruct (LEM (f[k] = k)) as [Q4 | Q4].
    + apply (S3 _ Q3 Q4).
    + destruct (LEM (∃ p, p ∈ k ∧ f[p] = k)) as [Q5 | Q5].
      - destruct Q5 as [p [R1 R2]].
        assert (k ≠ p) as R3.
        { intros R4.
          apply (nin_self k).
          apply (eq_cr (λ x, x ∈ k) R4 R1). }
        apply (eq_cl (λ x, x = S(k))
          (fn_swap_ran _ _ _ S1
            (eq_cr (λ x, k ∈ x) S2 (suc_i1 k))
            (eq_cr (λ x, p ∈ x) S2 (suc_i2 _ _ R1)))).
        apply S3.
        * apply (fn_swap_inj _ _ _ _ _ Q3 (suc_i1 k) (suc_i2 _ _ R1) R3).
        * apply (eq_cl (λ x, (f \ J{⟨k, f[k]⟩} \ J{⟨p, f[p]⟩} ∪ J{⟨p, f[k]⟩} ∪ J{ ⟨k, f[p]⟩})[k] = x) R2).
          apply (fn_swap_fval _ _ _ _ _ Q3 (suc_i1 k) (suc_i2 _ _ R1) R3).
      - pose (not_ex_all_not _ Q5) as Q6.
        assert (inj (f↾k) k k) as Q7.
        { split. split.
          + apply (restr_fn _ _ S1).
          + split.
            - apply (eq_cr (λ x, x = k) (restr_dom _ _)).
              apply (eq_cr (λ x, x ∩ k = k) S2).
              apply inter2_absorb_r.
              apply suc_i3.
            - intros y R1.
              destruct (ran_e _ _ R1) as [x R2].
              destruct (restr_e _ _ _ _ R2) as [R3 R4].
              destruct (not_and_or (Q6 x)) as [R5 | R5].
              * apply bot_e.
                apply (R5 R4).
              * pose (S4 _ (ran_i2 _ _ _ R3)) as R6.
                destruct (suc_e _ _ R6) as [R7 | R7].
                ++apply bot_e.
                  apply R5.
                  apply eq_s.
                  apply (fval_i _ _ _ S1 (eq_cl (λ y, ⟨x, y⟩ ∈ f) R7 R3)).
                ++apply R7.
          + apply (restr_sing_rot _ _ S5). }
        assert (f[k] ∈ k) as Q8.
        { pose (fval_ran _ _ S1 (eq_cr (λ x , k ∈ x) S2 (suc_i1 k))) as R1.
          destruct (suc_e _ _ (S4 _ R1)) as [R2 | R2].
          + apply bot_e.
            apply (Q4 R2).
          + apply R2. }
        pose (eq_cr (λ x, f[k] ∈ x) (Q2 _ Q7) Q8) as Q9.
        destruct (ran_e _ _ Q9) as [xx Q10].
        destruct (restr_e _ _ _ _ Q10) as [Q11 Q12].
        pose (fval_i2 _ _ S1 (eq_cr (λ x , k ∈ x) S2 (suc_i1 k))) as Q13.
        pose (S5 _ _ _ Q13 Q11) as Q14.
        apply bot_e.
        apply (nin_self k).
        apply (eq_cr (λ x, x ∈ k) Q14 Q12).
  }
  destruct P3 as [F P4].
  destruct (bij_e _ _ _ P4) as [_ P5].
  destruct P4 as [_ [P6 _]].
  pose (inj_ran_exten _ _ _ _ P5 (psub_e _ _ P2)) as P7.
  pose (induction_principle _ I1 I2 _ P1 _ P7) as P8.
  apply (psub_ir m).
  apply (eq_cr (λ x, m ⊂ x) (eq_t (eq_s P6) P8)).
  apply P2.
Qed.

