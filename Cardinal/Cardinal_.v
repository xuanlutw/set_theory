Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Nat.
Require Import Ordinal.Ordinal.
Require Import Cardinal.Equinumerous.

(* Hartog's Lemma *)
Lemma ex_ordinal_not_dominal: ∀ A, ∃ B, Ord B ∧ ~(B ≼ A).
Proof.
  intros A.
  pose ({x: 𝒫(A ⨉ A) ⨉ 𝒫(A)| ∃ R, ∃ S, x = ⟨R, S⟩ ∧ wo R S}) as W.
  pose (λ x, λ y, ∃ R, ∃ S, x = ⟨R, S⟩ ∧ y = EI(R, S)) as P.
  assert (∀ x, ∀ y1, ∀ y2, x ∈ W → P x y1 → P x y2 → y1 = y2) as P1.
  { intros x y1 y2 P1 P2 P3.
    destruct P2 as [R1 [S1 [Q11 Q12]]].
    destruct P3 as [R2 [S2 [Q21 Q22]]].
    pose (eq_t (eq_s Q11) Q21) as Q1.
    apply (eq_cr (λ x, x = y2) Q12).
    apply (eq_cr (λ x, EI(x, S1) = y2) (opair_eq_el _ _ _ _ Q1)).
    apply (eq_cr (λ x, EI(R2, x) = y2) (opair_eq_er _ _ _ _ Q1)).
    apply (eq_cr (λ x, EI(R2, S2) = x) Q22).
    apply eq_r. }
  destruct (ax_replace _ _ P1) as [B P2].
  assert (∀ b, b ∈ B → ∃ R, ∃ S, S ⊆ A ∧ wo R S ∧ b = EI(R, S)) as P3.
  { intros b Q1.
    destruct (P2 b) as [Q2 _].
    destruct (Q2 Q1) as [x [Q3 [R [S [Q4 Q5]]]]].
    destruct (sub_e _ _ _ Q3) as [Q8 [R' [S' [Q6 Q7]]]].
    pose (eq_t (eq_s Q4) Q6) as Q9.
    exists R.
    exists S.
    split.
    + destruct (cp_e2 _ _ _ _ (eq_cl (λ x, x ∈ (𝒫(A ⨉ A) ⨉ 𝒫(A))) Q4 Q8))
        as [_ Q10].
      apply power_e.
      apply Q10.
    + split.
      - apply (eq_cr (λ x, wo x S) (opair_eq_el _ _ _ _ Q9)).
        apply (eq_cr (λ x, wo R' x) (opair_eq_er _ _ _ _ Q9)).
        apply Q7.
      - apply Q5. }
  assert (∀ b, b ∈ B → Ord b) as P4.
  { intros b Q1.
    destruct (P3 _ Q1) as [R [S [_ [Q2 Q3]]]].
    exists R.
    exists S.
    split.
    + apply Q2.
    + apply Q3. }
  assert (∀ b, b ∈ B → b ≼ A) as P5.
  { intros b Q1.
    destruct (P3 _ Q1) as [R [S [Q2 [Q3 Q4]]]].
    pose (id_inj_exten _ _ Q2) as Q5.
    pose (eps_bij).
    pose (comp_inj).
    exists ((id S) ∘ (inv (E(R, S)))).
    apply (comp_inj _ _ _ S).
    + apply bij_e.
      apply inv_bij.
      apply (eq_cr (λ x, bij (E(R, S)) S x) Q4).
      apply (eps_bij _ _ Q3).
    + apply (id_inj_exten _ _ Q2). }
  assert (∀ b, Ord b → b ≼ A → b ∈ B) as P6.
  { intros b Q1 [f Q2].
    apply P2.
    destruct (isom_bij_ex_rel (ER(b)) _ _ _ (inj_bij _ _ _ Q2)) as [S [Q3 Q4]].
    pose (isom_wo _ _ _ _ (ord_wo _ Q1) Q4) as Q5.
    exists (⟨S, ran(f)⟩).
    split.
    + apply sub_i.
      destruct Q2 as [[_ [_ Q2]] _].
      - apply cp_i.
          apply power_i.
          apply (sub_t _ _ _ Q3 (cp_sub _ _ _ _ Q2 Q2)).
        * apply power_i.
          apply Q2.
      - exists S.
        exists (ran(f)).
        split.
        * apply eq_r.
        * apply Q5.
    + exists S.
      exists (ran(f)).
      split.
      - apply eq_r.
      - apply (eq_cl (λ x, b = x) (wo_isom_eps_eq _ _ _ _ (ord_wo _ Q1) Q5 Q4)).
        apply (ord_e2 _ Q1). }
  apply nn_e.
  intros P7.
  pose (not_ex_all_not _ P7) as P8.
  apply no_ord_set.
  exists B.
  intros b.
  split.
  + intros P9.
    apply (P6 _ P9).
    apply nn_e.
    apply ((imp_i (not_and_or (P8 b))) P9).
  + intros P9.
    apply (P4 _ P9).
Qed.
