Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Nat.
Require Import Structure.Structure.
Require Import Ordinal.Ordinal.

Require dpdgraph.dpdgraph.

Definition eqnum  (A B: J) := ∃ F, F ∈ A ↦ᵇ B.
Notation   "A ≈ B"         := (eqnum A B).
Definition neqnum (A B: J) := (~(A ≈ B)).
Notation   "A ≉ B"         := (neqnum A B).

Definition domin  (A B: J) := ∃ F, F ∈ A ↦ⁱ B.
Notation   "A ≼ B"         := (domin A B).
Definition ndomin (A B: J) := (~(A ≼ B)).
Notation   "A ⋠ B"         := (ndomin A B).

(* Equinumerous *)
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
  intros A [f P1].
  pose ({x: A| x ∉ f[x]}) as B.
  assert (B ∉ ran(f)) as P2.
  { intros Q1.
    destruct (ran_e _ _ Q1) as [x Q2].
    pose (fval_i _ _ _ (bij_fn _ _ _ P1) Q2) as Q3.
    destruct (LEM (x ∈ f[x])) as [Q4 | Q4].
    + pose (eq_cl (λ y, x ∈ y) Q3 Q4) as Q5.
      destruct (sub_e _ _ _ Q5) as [_ Q6].
      apply (Q6 Q4).
    + apply (eq_cl (λ y, x ∉ y) Q3 Q4).
      apply sub_i.
      * apply (eq_cl (λ y, x ∈ y) (bij_dom _ _ _ P1)).
        apply (dom_i _ _ _ Q2).
      * apply Q4. }
  apply P2.
  apply (eq_cr (λ y, B ∈ y) (bij_ran _ _ _ P1)).
  apply power_i.
  apply sub_e1.
Qed.

Lemma eqnum_eps_image: ∀ R, ∀ A, wo R A → A ≈ EI(R, A).
Proof.
  intros R A P1.
  exists (E(R, A)).
  apply (eps_bij _ _ P1).
Qed.

Definition finite   (A: J) := ∃ n, n ∈ ω ∧ A ≈ n.
Definition infinite (A: J) := ~(finite A).

Lemma pigenhole: ∀ n, ∀ m, n ∈ ω → m ⊂ n → n ≉ m.
Proof.
  intros n m P1 P2 P3.
  pose (λ x, ∀ f, f ∈ x ↦ⁱ x → ran(f) = x) as P.
  assert (P 𝟢) as I1.
  { intros f Q1.
    apply (sub_empty_empty _ (inj_ran _ _ _ Q1)). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 f Q3.
    pose (inj_fn _ _ _ Q3) as S1.
    pose (inj_dom _ _ _ Q3) as S2.
    assert (∀ f, f ∈ (S(k)) ↦ⁱ (S(k)) → f[k] = k → ran(f) = S(k)) as S3.
    { intros f0 R1 R2.
      pose (f0 \ `{⟨k, f0[k]⟩}) as f1.
      pose (inj_kick _ _ _ _ R1 (suc_i1 k)) as Q5.
      pose (eq_cl (λ s, f1 ∈ ((S(k)) \ `{k}) ↦ⁱ ((S(k)) \ `{s})) R2 Q5) as Q6.
      pose (eq_cl (λ s, f1 ∈ s ↦ⁱ s) (suc_kick_self k) Q6) as Q7.
      pose (sing_sub_i _ _ (fval_i2 _ _ (inj_fn _ _ _ R1) 
        (eq_cr (λ x, k ∈ x) (inj_dom _ _ _ R1) (suc_i1 k)))) as Q8.
      apply (eq_cl (λ s, ran(s) = S(k)) (compl_union2_annihilate _ _ Q8)).
      apply (eq_cr (λ s, s = S(k)) (union2_ran _ _)).
      apply (eq_cr (λ s, s ∪ ran(`{⟨k, f0[k]⟩}) = S(k)) (Q2 _ Q7)).
      apply (eq_cr (λ s, k ∪ s = S(k)) (sing_pair_ran _ _)).
      apply (eq_cr (λ s, k ∪ `{s} = S(k)) R2).
      apply eq_r. }
    pose (inj_ran _ _ _ Q3) as S4.
    pose (inj_sing_rot _ _ _ Q3) as S5.
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
        * apply (eq_cl (λ x, (f \ `{⟨k, f[k]⟩} \ `{⟨p, f[p]⟩} ∪ `{⟨p, f[k]⟩} ∪ `{ ⟨k, f[p]⟩})[k] = x) R2).
          apply (fn_swap_fval _ _ _ _ _ Q3 (suc_i1 k) (suc_i2 _ _ R1) R3).
      - pose (not_ex_all_not _ Q5) as Q6.
        assert ((f↾k) ∈ k ↦ⁱ k) as Q7.
        { apply inj_i.
          + apply (restr_fn _ _ S1).
          + apply (eq_cr (λ x, x = k) (restr_dom _ _)).
            apply (eq_cr (λ x, x ∩ k = k) S2).
            apply inter2_absorb_r.
            apply suc_i3.
          + intros y R1.
            destruct (ran_e _ _ R1) as [x R2].
            destruct (restr_e _ _ _ _ R2) as [R3 R4].
            destruct (not_and_or (Q6 x)) as [R5 | R5].
            - apply bot_e.
              apply (R5 R4).
            - pose (S4 _ (ran_i _ _ _ R3)) as R6.
              destruct (suc_e _ _ R6) as [R7 | R7].
              * apply bot_e.
                apply R5.
                apply (fval_i _ _ _ S1 (eq_cl (λ y, ⟨x, y⟩ ∈ f) R7 R3)).
              * apply R7.
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
  pose (inj_ran_exten _ _ _ _ P5 (psub_e _ _ P2)) as P7.
  pose (induction_principle _ I1 I2 _ P1 _ P7) as P8.
  apply (psub_ir m).
  apply (eq_cr (λ x, m ⊂ x) (eq_t (eq_s (bij_ran _ _ _ P4)) P8)).
  apply P2.
Qed.

Lemma finite_neqnum_psub: ∀ A, ∀ B, finite A → B ⊂ A → A ≉ B.
Proof.
  intros A B [n [P1 [f P2]]] P3 [g P4].
  pose (f⟦B⟧).
  destruct (psub_e2 _ _ P3) as [x [P5 P6]].
  apply (pigenhole n (f⟦B⟧) P1).
  + apply psub_i.
    - apply (eq_cl (λ x, f⟦B⟧ ⊆ x) (bij_ran _ _ _ P2)).
      apply (image_ran).
    - intros P7.
      destruct (bij_e _ _ _ P2) as [_ S0].
      (*destruct P2 as [[P8 [P9 _]] [P10 _]].*)
      pose (fval_ran _ _ (bij_fn _ _ _ P2) 
        (eq_cr (λ y, x ∈ y) (bij_dom _ _ _ P2) P6)) as P11.
      pose (eq_cl (λ y, f[x] ∈ y)
        (eq_t (bij_ran _ _ _ P2) (eq_s P7)) P11) as P12.
      destruct (image_e _ _ _ P12) as [x0 [P13 P14]].
      pose (fval_i _ _ _ (bij_fn _ _ _ P2) P13) as P15.
      pose (fval_inj _ _ _ _ _ S0 P6 (psub_e _ _ P3 _ P14) (eq_s P15)) as P16.
      apply P5.
      apply (eq_cr (λ x, x ∈ B) P16).
      apply P14.
  + exists (f ∘ (g ∘ f⁻¹)).
    pose (inv_bij _ _ _ P2) as P7.
    pose (comp_bij _ _ _ _ _ P7 P4) as P8.
    apply (comp_bij_weak _ _ _ _ _ _ P8 P2 (psub_e _ _ P3)).
Qed.

Lemma eqnum_psub_infinite: ∀ A, ∀ B, B ⊂ A → A ≈ B → infinite A.
Proof.
  intros A B P1 P2 P3.
  apply (finite_neqnum_psub _ _ P3 P1 P2).
Qed.

Lemma omega_infinite: infinite ω.
Proof.
  apply (eqnum_psub_infinite _ (ω \ `{𝟢})).
  + apply psub_i.
    - apply compl_psub.
      * apply sing_sub_i.
        apply empty_is_nat.
      * apply sing_nempty.
    - intros P1.
      pose (eq_cr (λ x, ∅ ∈ x) P1 empty_is_nat) as P2.
      destruct (compl_e _ _ _ P2) as [_ P3].
      apply P3.
      apply sing_i.
  + exists ({x: ω ⨉ ω| ∃ n, x = ⟨n, S(n)⟩}).
    apply bij_i.
    - split.
      * apply cp_sub_rel.
      * intros x y1 y2 P1 P2.
        destruct (sub_e _ _ _ P1) as [_ [n1 P3]].
        destruct (sub_e _ _ _ P2) as [_ [n2 P4]].
        apply (eq_cr (λ x, x = y2) (opair_eq_er _ _ _ _ P3)).
        apply (eq_cr (λ x, S(n1) = x) (opair_eq_er _ _ _ _ P4)).
        apply (eq_cl (λ x, S(x) = S(n2)) (opair_eq_el _ _ _ _ P3)).
        apply (eq_cl (λ y, S(x) = S(y)) (opair_eq_el _ _ _ _ P4)).
        apply eq_r.
    - apply sub_a.
      split.
      * apply (cp_sub_dom _ _ _ (sub_e1 _ _)).
      * intros n P1.
        apply (dom_i _ _ (S(n))).
        apply sub_i.
        ++apply (cp_i _ _ _ _ P1 (suc_is_nat _ P1)).
        ++exists n.
          apply eq_r.
    - apply sub_a.
      split.
      * intros y P1.
        destruct (ran_e _ _ P1) as [n P2].
        destruct (sub_e _ _ _ P2) as [P3 [n' P4]].
        apply compl_i.
        ++apply (cp_e2 _ _ _ _ P3).
        ++intros P5.
          apply (empty_not_suc n').
          apply (eq_t (sing_e _ _ P5) (opair_eq_er _ _ _ _ P4)).
      * intros x P1.
        destruct (compl_e _ _ _ P1) as [P2 P3].
        destruct (nat_is_suc _ P2 (neq_s (nsing_e _ _ P3))) as [n [P4 P5]].
        apply (ran_i _ n).
        apply sub_i.
        ++apply (cp_i _ _ _ _ P4 P2).
        ++exists n.
          apply (opair_eq_i _ _ _ _ (eq_r _) P5).
    - intros n1 n2 y P1 P2.
      destruct (sub_e _ _ _ P1) as [P5 [n1' P3]].
      destruct (sub_e _ _ _ P2) as [P6 [n2' P4]].
      apply (eq_cr (λ x, x = n2) (opair_eq_el _ _ _ _ P3)).
      apply (eq_cr (λ x, n1' = x) (opair_eq_el _ _ _ _ P4)).
      apply (suc_unique).
      * apply (eq_cl (λ x, x ∈ ω) (opair_eq_el _ _ _ _ P3)).
        apply (cp_e2 _ _ _ _ P5).
      * apply (eq_cl (λ x, x ∈ ω) (opair_eq_el _ _ _ _ P4)).
        apply (cp_e2 _ _ _ _ P6).
      * apply (eq_cl (λ x, x = S(n2')) (opair_eq_er _ _ _ _ P3)).
        apply (eq_cl (λ x, y = x) (opair_eq_er _ _ _ _ P4)).
        apply eq_r.
Qed.

Lemma finite_eqnum_unique: ∀ A, ∀ n, ∀ m, finite A → n ∈ ω → m ∈ ω → A ≈ n
  → A ≈ m → n = m.
Proof.
  intros A n m P1 P2 P3 P4 P5.
  pose (eqnum_t _ _ _ (eqnum_s _ _ P4) P5) as P6.
  destruct (nat_less_tricho_weak _ _ P2 P3) as [P7 | [P7 | P7]].
  + destruct (sub_e2 _ _ (trans_e2 _ (nat_is_trans _ P3) _ (nat_less_e _ _ P7))) as [P8 | P8].
    - apply bot_e.
      apply (pigenhole _ _ P3 P8).
      apply (eqnum_s _ _ P6).
    - apply P8.
  + apply P7.
  + destruct (sub_e2 _ _ (trans_e2 _ (nat_is_trans _ P2) _ (nat_less_e _ _ P7))) as [P8 | P8].
    - apply bot_e.
      apply (pigenhole _ _ P2 P8).
      apply P6.
    - apply (eq_s P8).
Qed.

Lemma eqnum_sing_pair: ∀ x, ∀ y, `{x} ≈ `{y}.
Proof.
  intros x y.
  exists (`{⟨x, y⟩}).
  apply sing_pair_bij.
Qed.

Lemma eqnum_union2: ∀ A, ∀ B, ∀ C, ∀ D, A ≈ B → C ≈ D → A ∩ C = ∅ → B ∩ D = ∅
  → A ∪ C ≈ B ∪ D.
Proof.
  intros A B C D [f P1] [g P2] P3 P4.
  exists (f ∪ g).
  apply (union2_bij _ _ _ _ _ _ P1 P2 P3 P4).
Qed.

Lemma eqnum_switch: ∀ S, ∀ s, ∀ a, s ∈ S → a ∉ S → S ≈ S \ `{s} ∪ `{a}.
Proof.
  intros S s a P1 P2.
  apply (eq_cl (λ x, x ≈ S \ `{s} ∪ `{a}) 
    (compl_union2_annihilate _ _ (sing_sub_i _ _ P1))).
  apply eqnum_union2.
  + apply eqnum_r.
  + apply eqnum_sing_pair.
  + apply (eq_cr (λ x, x = ∅) (inter2_s _ _)).
    apply inter2_empty.
    intros x P3 P4.
    destruct (compl_e _ _ _ P4) as [_ P5].
    apply (P5 P3).
  + apply (eq_cr (λ x, x = ∅) (inter2_s _ _)).
    apply inter2_empty.
    intros x P3 P4.
    destruct (compl_e _ _ _ P4) as [P5 _].
    apply P2.
    apply (eq_cr (λ x, x ∈ S) (sing_e _ _ P3) P5).
Qed.

Lemma nat_psub_eqnum_nat: ∀ m, ∀ A, m ∈ ω → A ⊂ m → ∃ n, n ∈ ω ∧ n <ₙ m ∧ A ≈ n.
Proof.
  intros m A P1.
  pose (λ k, ∀ s, s ⊂ k → ∃ t, t ∈ ω ∧ t <ₙ k ∧ s ≈ t) as P.
  assert (P 𝟢) as I1.
  { intros s Q1.
    destruct (psub_e2 _ _ Q1) as [x [_ Q2]].
    apply bot_e.
    apply (empty_i _ Q2). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 s Q3.
    destruct (LEM (k ∈ s)) as [Q4 | Q4].
    + destruct (LEM (∀ x, x ∈ k → x ∈ s)) as [Q5 | Q5].
      - destruct (psub_e2 _ _ Q3) as [x [Q6 Q7]].
        destruct (suc_e _ _ Q7) as [Q8 | Q8].
        * apply bot_e.
          apply (Q6 (eq_cr (λ x, x ∈ s) Q8 Q4)).
        * apply bot_e.
          apply (Q6 (Q5 _ Q8)).
      - destruct (not_all_ex_not _ Q5) as [x Q6].
        destruct (nimp_e Q6) as [Q7 Q8].
        assert (s \ `{k} ∪ `{x} ⊆ k) as Q9_.
        { intros xx R1.
          destruct (union2_e _ _ _ R1) as [R2 | R2].
          + destruct (compl_e _ _ _ R2) as [R3 R4].
            destruct (suc_e _ _ (psub_e _ _ Q3 _ R3)) as [R5 | R5].
            - apply bot_e.
              apply ((neq_s (nsing_e _ _ R4)) R5).
            - apply R5.
          + apply (eq_cl (λ x, x ∈ k) (sing_e _ _ R2) Q7). }
        destruct (sub_e2 _ _ Q9_) as [Q9 | Q9].
        * destruct (Q2 _ Q9) as [t [Q10 [Q11 Q12]]].
          exists t.
          repeat split.
          ++apply Q10.
          ++apply (nat_l_l_t _ _ _ Q10 Q1 (suc_is_nat _ Q1) Q11 (less_suc _ Q1)).
          ++apply (eqnum_t _ (s \ `{k} ∪ `{x}) _).
            --apply (eqnum_switch _ _ _ Q4 Q8).
            --apply Q12.
        * exists k.
          repeat split.
          ++apply Q1.
          ++apply (less_suc _ Q1).
          ++apply (eq_cl (λ x, s ≈ x) Q9).
            apply (eqnum_switch _ _ _ Q4 Q8).
    + assert (s ⊆ k) as Q5.
      { intros x R1.
        pose (psub_e _ _ Q3 _ R1) as R2.
        destruct (suc_e _ _ R2) as [R3 | R3].
        + apply bot_e.
          apply (Q4 (eq_cl (λ x, x ∈ s) R3 R1)).
        + apply R3. }
      destruct (sub_e2 _ _ Q5) as [Q6 | Q6].
      - destruct (Q2 _ Q6) as [t [Q7 [Q8 Q9]]].
        exists t.
        repeat split.
        * apply Q7.
        * apply (nat_l_l_t _ _ _ Q7 Q1 (suc_is_nat _ Q1) Q8 (less_suc _ Q1)).
        * apply Q9.
      - exists k.
        repeat split.
        * apply Q1.
        * apply (less_suc _ Q1).
        * apply (eq_cr (λ x, x ≈ k) Q6 (eqnum_r _)). }
  apply (induction_principle _ I1 I2 _ P1).
Qed.

Lemma finite_sub_finite: ∀ A, ∀ B, finite A → B ⊆ A → finite B.
Proof.
  intros A B P1 P2.
  destruct (sub_e2 _ _ P2) as [P3 | P3].
  + destruct P1 as [n [Q1 [f Q2]]].
    destruct (nat_psub_eqnum_nat _ (f⟦B⟧) Q1 (image_bij_psub _ _ _ _ Q2 P3))
      as [n' [Q3 [Q4 Q5]]].
    exists n'.
    split.
    - apply Q3.
    - apply (eqnum_t _ (f⟦B⟧)).
      * exists (f↾B).
        apply (restr_bij _ _ _ _ Q2 P2).
      * apply Q5.
  + apply (eq_cr _ P3).
    apply P1.
Qed.
(*----------------------------------------------------------------------------*)

(* Dominate *)
Lemma domin_r: ∀ A, A ≼ A.
Proof.
  intros A.
  exists (id A).
  apply id_is_inj.
Qed.

Lemma domin_t: ∀ A, ∀ B, ∀ C, A ≼ B → B ≼ C → A ≼ C.
Proof.
  intros A B C [F P1] [G P2].
  exists (G ∘ F).
  apply (comp_inj _ _ _ _ _ P1 P2).
Qed.

(* Schroder Bernstin *)
Lemma domin_a: ∀ A, ∀ B, A ≼ B → B ≼ A → A ≈ B.
Proof.
  intros A B [F P1] [G P2].
  pose ({x: 𝒫(A) ⨉ 𝒫(A)| ∃ y, x = ⟨y, G⟦F⟦y⟧⟧⟩}) as M.
  assert (M ∈ (𝒫(A)) ↦ (𝒫(A))) as P3.
  { apply fmap_i.
    + split.
      - apply cp_sub_rel.
      - intros x y1 y2 Q1 Q2.
        destruct (sub_e _ _ _ Q1) as [_ [x1 Q3]].
        destruct (sub_e _ _ _ Q2) as [_ [x2 Q4]].
        apply (eq_cr (λ x, x = y2) (opair_eq_er _ _ _ _ Q3)).
        apply (eq_cr (λ x, G⟦F⟦x1⟧⟧ = x) (opair_eq_er _ _ _ _ Q4)).
        apply (eq_cl (λ x, G⟦F⟦x⟧⟧ = G⟦F⟦x2⟧⟧)
          (opair_eq_el _ _ _ _ Q3)).
        apply (eq_cl (λ y, G⟦F⟦x⟧⟧ = G⟦F⟦y⟧⟧)
          (opair_eq_el _ _ _ _ Q4)).
        apply eq_r.
    + apply sub_a.
      split.
      - apply (cp_sub_dom _ _ _ (sub_e1 _ _)).
      - intros x P3.
        apply (dom_i _ _ (G⟦F⟦x⟧⟧)).
        apply sub_i.
        * apply (cp_i _ _ _ _ P3).
          apply power_i.
          apply (sub_t _ _ _ (image_ran _ _) (inj_ran _ _ _ P2)).
        * exists x.
          apply eq_r.
    + apply (cp_sub_ran _ _ _ (sub_e1 _ _)). }
  pose (A \ ran(G)) as C0.
  assert (C0 ∈ 𝒫(A)) as P4.
  { apply power_i.
    intros x Q1.
    destruct (compl_e _ _ _ Q1) as [Q2 _].
    apply Q2. }
  destruct (recursion_thm (𝒫(A)) C0 M) as [M' P5].
  destruct (P5 P4 P3) as [P6 [P7 P8]].
  pose (∪ran(M')) as C.
  pose ((F↾C) ∪ ((inv G)↾(A \ C))) as H.
  assert (dom(H) = A) as P9.
  { apply sub_a.
    split.
    + apply (eq_cr (λ x, x ⊆ A) (union2_dom _ _)).
      apply union2_sub.
      - apply (eq_cl (λ x, dom(F↾C) ⊆ x) (inj_dom _ _ _ P1)).
        apply (eq_cr (λ x, x ⊆ dom(F)) (restr_dom _ _)).
        apply (inter2_sub_l).
      - apply (eq_cr (λ x, x ⊆ A) (restr_dom _ _)).
        apply (eq_cr (λ x, x ∩ (A \ C) ⊆ A) (inv_dom _)).
        apply (sub_t _ _ _ (inter2_sub_l _ _)).
        apply (inj_ran _ _ _ P2).
    + intros x Q1.
      destruct (LEM (x ∈ C)) as [Q2 | Q2].
      - apply (dom_i _ _ (F[x])).
        apply union2_il.
        apply restr_fval2.
        * apply (inj_fn _ _ _ P1).
        * apply (eq_cr (λ y, x ∈ y) (inj_dom _ _ _ P1) Q1).
        * apply Q2.
      - apply (dom_i _ _ (G⁻¹[x])).
        apply union2_ir.
        apply restr_fval2.
        * apply inv_fn.
          apply (inj_sing_rot _ _ _ P2).
        * apply (eq_cr (λ y, x ∈ y) (inv_dom _)).
          apply nn_e.
          intros Q3.
          apply Q2.
          apply union_i.
          exists (M'[∅]).
          split.
          ++apply (fval_codom _ ω).
            --apply (eq_cl (λ x, M' ∈ x ↦(ran(M'))) (fmap_dom _ _ _ P6)).
              apply (fmap_r _ (fmap_fn _ _ _ P6)).
            --apply empty_is_nat.
          ++apply (eq_cr (λ y, x ∈ y) P7).
            apply (compl_i _ _ _ Q1 Q3).
        * apply (compl_i _ _ _ Q1 Q2). }
  exists H.
  apply bij_i.
  + apply piecewise_function.
    - apply restr_fn.
      apply (inj_fn _ _ _ P1).
    - apply restr_fn.
      apply inv_fn.
      apply (inj_sing_rot _ _ _ P2).
    - apply (eq_cr (λ x, x ∩ dom((inv G)↾(A \ C)) = ∅) (restr_dom _ _)).
      apply (eq_cr (λ x, (dom(F) ∩ C) ∩ x = ∅) (restr_dom _ _)).
      apply empty_unique.
      intros x Q1.
      destruct (inter2_e _ _ _ Q1) as [Q2 Q3].
      destruct (inter2_e _ _ _ Q2) as [_ Q4].
      destruct (inter2_e _ _ _ Q3) as [_ Q5].
      destruct (compl_e _ _ _ Q5) as [_ Q6].
      apply (Q6 Q4).
  + apply P9.
  + apply sub_a.
    split.
    - apply (eq_cr (λ x, x ⊆ B) (union2_ran _ _)).
      apply union2_sub.
      * apply (sub_t _ _ _ (image_ran _ _) (inj_ran _ _ _ P1)).
      * apply (eq_cl (λ x, ran((inv G)↾(A \ C)) ⊆ x) (inj_dom _ _ _ P2)).
        apply (eq_cl (λ x, ran((inv G)↾(A \ C)) ⊆ x) (inv_ran _)).
        apply (image_ran).
    - intros y Q1.
      destruct (LEM (∃ n, n ∈ ω ∧ y ∈ F⟦M'[n]⟧)) as [[n [Q2 Q3]] | Q2].
      * destruct (image_e _ _ _ Q3) as [x [Q4 Q5]].
        apply (eq_cr (λ x, y ∈ x) (union2_ran _ _)).
        apply union2_il.
        apply (ran_i _ x).
        apply restr_i.
        ++apply Q4.
        ++apply union_i.
          exists (M'[n]).
          split.
          --apply fval_ran.
            **apply (fmap_fn _ _ _ P6).
            **apply (eq_cr (λ x, n ∈ x) (fmap_dom _ _ _ P6)).
              apply Q2.
          --apply Q5.
      * pose (not_ex_all_not _ Q2) as Q3.
        apply (eq_cr (λ x, y ∈ x) (union2_ran _ _)).
        apply union2_ir.
        apply (ran_i _ (G[y])).
        apply restr_i.
        ++apply inv_i.
          apply fval_i2.
          --apply (inj_fn _ _ _ P2).
          --apply (eq_cr (λ x, y ∈ x) (inj_dom _ _ _ P2) Q1).
        ++apply compl_i.
          --apply (fval_codom _ B).
            **apply (inj_fmap _ _ _ P2).
            **apply Q1.
          --intros Q4.
            destruct (union_e _ _ Q4) as [m [Q5 Q6]].
            destruct (ran_e _ _ Q5) as [n Q7].
            destruct (LEM (n = 𝟢)) as [Q8 | Q8].
            **assert (G[y] ∈ ran(G)) as Q9.
              { apply fval_ran.
                + apply (inj_fn _ _ _ P2).
                + apply (eq_cr (λ x, y ∈ x) (inj_dom _ _ _ P2) Q1). }
              assert (G[y] ∉ ran(G)) as Q10.
              { pose (eq_cr (λ x, G[y] ∈ x)
                  (fval_i _ _ _ (fmap_fn _ _ _ P6) Q7) Q6) as R1.
                pose (eq_cl (λ x, G[y] ∈ M'[x]) Q8 R1) as R2.
                pose (eq_cl (λ x, G[y] ∈ x) P7 R2) as R3.
                destruct (compl_e _ _ _ R3) as [_ R4].
                apply R4. }
              apply (Q10 Q9).
            **assert (n ∈ ω) as Q9.
              { apply (eq_cl (λ x, n ∈ x) (fmap_dom _ _ _ P6)).
                apply (dom_i _ _ _ Q7). }
              destruct (nat_is_suc _ Q9 Q8) as [n' [Q10 Q11]].
              apply (Q3 n').
              repeat split.
              { apply Q10. }
              { apply (image_e2 _ _ _ _ _ P2 Q1).
                assert (M[M'[n']] = G⟦F⟦M'[n']⟧⟧) as R1.
                { apply fval_i.
                  + apply (fmap_fn _ _ _ P3).
                  + apply sub_i.
                    - apply cp_i.
                      * apply (fval_codom _ _ _ _ P6 Q10).
                      * apply power_i.
                        apply (image_fmap _ B).
                       apply (inj_fmap _ _ _ P2).
                    - exists (M'[n']).
                      apply eq_r. }
                assert (M'[n] = m) as R2.
                { apply fval_i.
                  + apply (fmap_fn _ _ _ P6).
                  + apply Q7. }
                apply (eq_cl (λ x, G[y] ∈ x) R1).
                apply (eq_cl (λ x, G[y] ∈ x) (P8 _ Q10)).
                apply (eq_cl (λ x, G[y] ∈ M'[x]) Q11).
                apply (eq_cr (λ x, G[y] ∈ x) R2).
                apply Q6. }
  + assert (∀ x1, ∀ x2, ∀ y, ⟨x1, y⟩ ∈ F↾C → ⟨x2, y⟩ ∈ (inv G)↾(A \ C) → x1 = x2)
      as Q0.
    { intros x1 x2 y Q1 Q2.
      destruct (restr_e _ _ _ _ Q1) as [Q3 Q4].
      destruct (union_e _ _ Q4) as [m [Q5 Q6]].
      destruct (ran_e _ _ Q5) as [n Q7].
      assert (y ∈ F⟦m⟧) as Q8.
      { assert (F[x1] = y) as R1.
        { apply fval_i.
          + apply (inj_fn _ _ _ P1).
          + apply Q3. }
        apply (eq_cl (λ x, x ∈ F⟦m⟧) R1).
        apply image_i2.
        + apply (inj_fn _ _ _ P1).
        + apply (dom_i _ _ _ Q3).
        + apply Q6. }
      destruct (restr_e _ _ _ _ Q2) as [Q9 Q10].
      destruct (compl_e _ _ _ Q10) as [Q11 Q12].
      assert (x2 ∈ G⟦F⟦m⟧⟧) as Q13.
      { assert (G[y] = x2) as R1.
        { apply fval_i.
          + apply (inj_fn _ _ _ P2).
          + apply (inv_e _ _ _ Q9). }
        apply (eq_cl (λ x, x ∈ G⟦F⟦m⟧⟧) R1).
        apply image_i2.
        + apply (inj_fn _ _ _ P2).
        + apply (dom_i _ _ _ (inv_e _ _ _ Q9)).
        + apply Q8. }
      assert (n ∈ ω) as Q14.
      { apply (eq_cl (λ x, n ∈ x) (fmap_dom _ _ _ P6)).
        apply (dom_i _ _ _ Q7). }
      assert (x2 ∈ C) as Q15.
      { apply union_i.
        exists (G⟦F⟦m⟧⟧).
        split.
        + apply (ran_i _ (S(n))).
          apply fval_e.
          - assert (M[m] = G⟦F⟦m⟧⟧) as R1.
            { apply fval_i.
              apply (fmap_fn _ _ _ P3).
              apply sub_i.
              + apply cp_i.
                - apply ((fmap_ran _ _ _ P6) _ Q5).
                - apply power_i.
                  apply (sub_t _ _ _ (image_ran _ _) (inj_ran _ _ _ P2)).
              + exists m.
                apply eq_r. }
            assert (M'[n] = m) as R2.
            { apply fval_i.
              + apply (fmap_fn _ _ _ P6).
              + apply Q7. }
            apply (eq_cl (λ x, _ = x) R1).
            apply (eq_cl (λ x, _ = M[x]) R2).
            apply P8.
            apply Q14.
          - apply (fmap_fn _ _ _ P6).
          - apply (eq_cr (λ x, S(n) ∈ x) (fmap_dom _ _ _ P6)).
            apply (suc_is_nat _ Q14).
        + apply Q13. }
      apply bot_e.
      apply (Q12 Q15). }
    intros x1 x2 y Q1 Q2.
    destruct (union2_e _ _ _ Q1) as [Q3 | Q3].
    - destruct (union2_e _ _ _ Q2) as [Q4 | Q4].
      * destruct (restr_e _ _ _ _ Q3) as [Q5 _].
        destruct (restr_e _ _ _ _ Q4) as [Q6 _].
        apply ((inj_sing_rot _ _ _ P1) _ _ _ Q5 Q6).
      * apply (Q0 _ _ _ Q3 Q4).
    - destruct (union2_e _ _ _ Q2) as [Q4 | Q4].
      * apply eq_s.
        apply (Q0 _ _ _ Q4 Q3).
      * destruct (restr_e _ _ _ _ Q3) as [Q5 _].
        destruct (restr_e _ _ _ _ Q4) as [Q6 _].
        apply ((inv_sing_val _ (fn_sing_val _ (inj_fn _ _ _ P2))) _ _ _ Q5 Q6).
Qed.

