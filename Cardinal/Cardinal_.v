Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Nat.
Require Import Ordinal.Ordinal.
Require Import Cardinal.Equinumerous.

Require dpdgraph.dpdgraph.

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

Theorem well_ord_thm: ∀ A, ∃ R, wo R A.
Proof.
  intros A.
  destruct (ex_ordinal_not_dominal A) as [Alpha [P1 P2]].
  destruct (ex_extra A) as [e P3].
  destruct (choice_fn_ex A) as [G [P4 [P5 P6]]].
  pose (λ x, λ y,
    ((A \ ran(x)) = ∅ ∧ y = e) ∨ ((A \ ran(x)) ≠ ∅ ∧ y = G[A \ ran(x)])) as P.
  assert (_G_unique P) as P7.
  { split.
    + intros x.
      destruct (LEM ((A \ ran(x)) = ∅)) as [Q1 | Q1].
      - exists e.
        left.
        apply (and_i Q1 (eq_r _)).
      - exists (G[A \ ran(x)]).
        right.
        apply (and_i Q1 (eq_r _)).
    + intros x y1 y2 [[Q1 Q2] | [Q1 Q2]] [[Q3 Q4] | [Q3 Q4]].
      - apply (eq_t Q2 (eq_s Q4)).
      - apply (bot_e _ (Q3 Q1)).
      - apply (bot_e _ (Q1 Q3)).
      - apply (eq_t Q2 (eq_s Q4)). }
  destruct (transfinite_recursion _ _ _ (ord_wo _ P1) P7) as [F [P8 [P9 P10]]].
  assert (∀ a1, ∀ a2, a1 ∈ a2 → a2 ∈ Alpha → F[a2] ≠ e → F[a1] ≠ e) as R1.
  { intros a1 a2 Q1 Q2 Q3 Q4.
    pose (ord_trans _ P1 _ _ Q1 Q2) as Q5.
    destruct (P10 _ Q5) as [[Q6 _] | [Q6 Q7]].
    + destruct (P10 _ Q2) as [[_ Q7] | [Q7 _]].
      - apply (Q3 Q7).
      - apply Q7.
        apply sub_empty_empty.
        apply (eq_cl (λ x, _ ⊆ x) Q6).
        apply compl_sub_reverse.
        apply image_sub.
        apply (seg_less_sub _ _ _ _ (wo_trans _ _ (ord_wo _ P1)) Q5 Q2
          (eps_rel_i _ _ _ Q5 Q2 Q1)).
    + destruct (compl_e _ _ _ (P6 _ Q6 (compl_sub _ _))) as [Q8 _].
      apply P3.
      apply (eq_cr (λ x, x ∈ A) (eq_t (eq_s Q4) Q7) Q8). }
  assert (∀ a1, ∀ a2, a1 ∈ a2 → a2 ∈ Alpha → F[a2] ≠ e → F[a1] ≠ F[a2]) as R2.
  { intros a1 a2 Q1 Q2 Q3 Q4.
    pose (ord_trans _ P1 _ _ Q1 Q2) as Q5.
    destruct (P10 _ Q2) as [[_ Q6] | [Q6 Q7]].
    + apply (Q3 Q6).
    + destruct (P10 _ Q5) as [[_ Q8] | [Q8 Q9]].
      - apply (R1 _ _ Q1 Q2 Q3 Q8).
      - pose P6.
        assert (F[a1] ∈ F⟦a2⟧) as Q10.
        { apply image_i.
          exists a1.
          split.
          + apply (fval_i2 _ _ P8 (eq_cr (λ x, a1 ∈ x) P9 Q5)).
          + apply Q1. }
        assert (F[a2] ∉ F⟦a2⟧) as Q11.
        { intros S1.
          destruct (image_e _ _ _ S1) as [a' [S2 S3]].
          pose (fval_i _ _ _ P8 S2) as S4.
          pose (eq_cr (λ x, x ∈ _) Q7 (P6 _ Q6 (compl_sub _ _))) as S5.
          destruct (compl_e _ _ _ S5) as [_ S7].
          pose (ord_trans _ P1 _ _ S3 Q2) as S8.
          apply S7.
          apply (eq_cr (λ x, x ∈ _) S4).
          apply ran_i.
          exists a'.
          apply restr_i.
          + apply (fval_i2 _ _ P8 (eq_cr (λ x, a' ∈ x) P9 S8)).
          + apply seg_i.
            - apply S8.
            - apply (eps_rel_i _ _ _ S8 Q2 S3). }
        apply Q11.
        apply (eq_cl (λ x, x ∈ _) Q4 Q10). }
  assert (e ∈ ran(F)) as R3.
  { apply nn_e.
    intros Q1.
    apply P2.
    exists F.
    split.
    + split.
      - apply P8.
      - split.
        * apply P9.
        * intros y Q2.
          destruct (ran_e _ _ Q2) as [x Q3].
          pose (fval_i _ _ _ P8 Q3) as Q4.
          destruct (P10 _ (eq_cl (λ y, x ∈ y) P9 (dom_i2 _ _ _ Q3)))
            as [[_ Q5] | [Q5 Q6]].
          ++apply bot_e.
            apply Q1.
            destruct (fval_e _ _ _ (eq_s Q5) P8 (dom_i2 _ _ _ Q3)) as [Q6 _].
            apply (ran_i2 _ _ _ Q6).
          ++apply (eq_cr (λ x, x ∈ A) Q4).
            apply (eq_cr (λ x, x ∈ A) Q6).
            apply (compl_sub _ _ _ (P6 _ Q5 (compl_sub _ _))).
    + intros x1 x2 y Q2 Q3.
      pose (eq_cl (λ x, _ ∈ x) P9 (dom_i2 _ _ _ Q2)) as Q4.
      pose (eq_cl (λ x, _ ∈ x) P9 (dom_i2 _ _ _ Q3)) as Q5.
      destruct (ord_tricho_weak _ _ (in_ord_ord _ _ P1 Q4)
        (in_ord_ord _ _ P1 Q5)) as [Q6 | [Q6 | Q6]].
      - apply bot_e.
        apply (R2 _ _ Q6 Q5).
        * intros Q7.
          apply Q1.
          destruct (fval_e _ _ _ (eq_s Q7) P8 (dom_i2 _ _ _ Q3)) as [Q8 _].
          apply (ran_i2 _ _ _ Q8).
        * apply (eq_t (eq_s (fval_i _ _ _ P8 Q2)) (fval_i _ _ _ P8 Q3)).
      - apply Q6.
      - apply bot_e.
        apply (R2 _ _ Q6 Q4).
        * intros Q7.
          apply Q1.
          destruct (fval_e _ _ _ (eq_s Q7) P8 (dom_i2 _ _ _ Q2)) as [Q8 _].
          apply (ran_i2 _ _ _ Q8).
        * apply (eq_t (eq_s (fval_i _ _ _ P8 Q3)) (fval_i _ _ _ P8 Q2)). }
  destruct (ran_e _ _ R3) as [xx R4].
  pose (eq_s (fval_i _ _ _ P8 R4)) as R5.
  destruct (wo_prop_seg (λ x, F[x] = e) _ _ _ (ord_wo _ P1)
    (eq_cl (λ x, xx ∈ x) P9 (dom_i2 _ _ _ R4)) R5) as [x0 [R6 [R7 R8]]].
  assert (bij (F↾(seg (ER(Alpha)) Alpha x0)) (seg (ER(Alpha)) Alpha x0) A) as R9.
  { apply bij_i2.
    + apply (restr_fn _ _ P8).
    + apply (eq_cr (λ x, x = _) (restr_dom _ _)).
      apply (eq_cr (λ x, x ∩ _ = _) P9).
      apply inter2_absorb_r.
      apply (seg_sub _ _ _ R6).
    + apply sub_a.
      split.
      - intros y Q1.
        destruct (ran_e _ _ Q1) as [x Q2].
        destruct (restr_e _ _ _ _ Q2) as [Q3 Q4].
        pose (seg_e1 _ _ _ _ R6 Q4) as Q5.
        destruct (P10 _ Q5) as [[_ Q6] | [Q6 Q7]].
        * apply bot_e.
          apply (R8 _ Q4 Q6).
        * destruct (compl_e _ _ _ (P6 _ Q6 (compl_sub _ _))) as [Q8 _].
          apply (eq_cr (λ y, y ∈ A) (fval_i _ _ _ P8 Q3)).
          apply (eq_cr (λ y, y ∈ A) Q7).
          apply Q8.
      - intros y Q1.
        destruct (P10 _ R6) as [[Q2 _] | [Q2 Q3]].
        * apply ((compl_empty _ _ Q2) _ Q1).
        * destruct (compl_e _ _ _ (P6 _ Q2 (compl_sub _ _))) as [Q4 _].
          apply bot_e.
          apply P3.
          apply (eq_cr (λ x, x ∈ A) (eq_t (eq_s R7) Q3)).
          apply Q4.
    + intros x1 x2 y Q1 Q2.
      destruct (restr_e _ _ _ _ Q1) as [Q3 Q4].
      destruct (restr_e _ _ _ _ Q2) as [Q5 Q6].
      pose (eq_cl (λ x, _ ∈ x) P9 (dom_i2 _ _ _ Q3)) as Q7.
      pose (eq_cl (λ x, _ ∈ x) P9 (dom_i2 _ _ _ Q5)) as Q8.
      destruct (ord_tricho_weak _ _ (in_ord_ord _ _ P1 Q7)
        (in_ord_ord _ _ P1 Q8)) as [Q9 | [Q9 | Q9]].
      - apply bot_e.
        apply (R2 _ _ Q9 Q8 (R8 _ Q6)).
        apply (eq_t (eq_s (fval_i _ _ _ P8 Q3)) (fval_i _ _ _ P8 Q5)).
      - apply Q9.
      - apply bot_e.
        apply (R2 _ _ Q9 Q7 (R8 _ Q4)).
        apply (eq_t (eq_s (fval_i _ _ _ P8 Q5)) (fval_i _ _ _ P8 Q3)). }
  destruct (isom_bij_ex_rel (ER(seg (ER(Alpha)) Alpha x0)) _ _ _ R9)
    as [R [R10 R11]].
  exists R.
  pose (wo_seg _ _ _ (ord_wo _ P1) R6) as R12.
  pose (eps_rel_eq _ _ (seg_sub (ER(Alpha)) _ _ R6)) as R13.
  pose (wo_rel_exten _ _ _ R13 R12) as R14.
  apply (isom_wo _ _ _ _ R14 R11).
Qed.

Lemma numeration: ∀ A, ∃ O, Ord O ∧ A ≈ O.
Proof.
  intros A.
  destruct (well_ord_thm A) as [R P1].
  exists (EI(R, A)).
  split.
  + exists R.
    exists A.
    split.
    - apply P1.
    - apply eq_r.
  + apply (eqnum_eps_image _ _ P1).
Qed.

Lemma cardinality_ex: ∀ A, ∃ O, Ord O ∧ A ≈ O ∧ 
  ∀ O', Ord O' → O' ≈ A → O = O' ∨ O ∈ O'.
Proof.
  intros A.
  destruct (numeration A) as [O0 [P1 P2]].
  destruct (LEM (∀ O, O ∈ O0 → ~(O ≈ A))) as [P3 | P3].
  + exists O0.
    repeat split.
    - apply P1.
    - apply P2.
    - intros O' P4 P5.
      destruct (ord_tricho_weak _ _ P1 P4) as [P6 | [P6 | P6]].
      * right.
        apply P6.
      * left.
        apply P6.
      * apply bot_e.
        apply ((P3 _ P6) P5).
  + destruct (not_all_ex_not _ P3) as [O1 P4].
    destruct (nimp_e P4) as [P5 P6].
    pose (nn_e P6) as P7.
    destruct (wo_prop_least (λ x, x ≈ A) _ _ _ (ord_wo _ P1) P5 P7)
      as [O2 [P8 [P9 P10]]].
    exists O2.
    repeat split.
    - apply (in_ord_ord _ _ P1 P8).
    - apply (eqnum_s _ _ P9).
    - intros O' Q1 Q2.
      pose (in_ord_ord _ _ P1 P8) as Q3.
      destruct (ord_tricho_weak _ _ Q3 Q1)
        as [Q4 | [Q4 | Q4]].
      * right.
        apply Q4.
      * left.
        apply Q4.
      * pose (ord_t _ _ _ Q1 Q3 P1 Q4 P8) as Q5.
        destruct (P10 _ Q5 Q2) as [Q6 | Q6].
        ++apply bot_e.
          apply (no_mutual_in O' O2).
          split.
          -- apply Q4.
          -- apply (eps_rel_e _ _ _ Q6).
        ++left.
          apply Q6.
Qed.

Definition cardinality (A: J) := (ex_outl (cardinality_ex A)).
Notation   "| A |"            := (cardinality A).
Definition Card        (A: J) := (∃ B, A = |B|).

Lemma cardinality_ord: ∀ A, Ord (|A|).
Proof.
  intros A.
  apply (ex_outr (cardinality_ex A)).
Qed.

Lemma cardinality_eqnum: ∀ A, A ≈ |A|.
Proof.
  intros A.
  apply (ex_outr (cardinality_ex A)).
Qed.

Lemma cardinality_least: ∀ A, ∀ O', Ord O' → O' ≈ A → |A| = O' ∨ |A| ∈ O'.
Proof.
  intros A.
  apply (ex_outr (cardinality_ex A)).
Qed.

Lemma cardinality_eq_eqnum: ∀ A, ∀ B, |A| = |B| → A ≈ B.
Proof.
  intros A B P1.
  pose (cardinality_eqnum A) as P2.
  pose (eq_cr (λ x, B ≈ x) P1 (cardinality_eqnum B)) as P3.
  apply (eqnum_t _ _ _ P2 (eqnum_s _ _ P3)).
Qed.

Lemma eqnum_cardinality_eq: ∀ A, ∀ B, A ≈ B → |A| = |B|.
Proof.
  intros A B P1.
  pose (cardinality_eqnum A) as P2.
  pose (eqnum_t _ _ _ (eqnum_s _ _ P1) P2) as P3.
  destruct (cardinality_least _ _ (cardinality_ord A) (eqnum_s _ _ P3))
    as [P4 | P4].
  + apply (eq_s P4).
  + pose (cardinality_eqnum B) as P5.
    pose (eqnum_t _ _ _ P1 P5) as P6.
    destruct (cardinality_least _ _ (cardinality_ord B) (eqnum_s _ _ P6))
      as [P7 | P7].
    - apply P7.
    - apply bot_e.
      apply (no_mutual_in _ _ (and_i P4 P7)).
Qed.

Lemma cardinality_self: ∀ A, |A| = |(|A|)|.
Proof.
  intros A.
  apply (eqnum_cardinality_eq _ _ (cardinality_eqnum A)).
Qed.

Lemma cardinality_card: ∀ A, Card (|A|).
Proof.
  intros A.
  exists A.
  apply eq_r.
Qed.

Lemma card_cardinality_self: ∀ A, Card A → |A| = A.
Proof.
  intros A [A' P1].
  apply (eq_cr (λ x, |x| = x) P1).
  apply eq_s.
  apply cardinality_self.
Qed.

Definition aleph_null := (|ω|).
Notation   "'ℵ₀'"     := aleph_null.
Definition card_add (A B: J) := |(A ⨉ `{𝟢}) ∪ (B ⨉ `{𝟣})|.
Notation   "A +c B"          := (card_add A B).
Definition card_mul (A B: J) := |A ⨉ B|.
Notation   "A ×c B"          := (card_mul A B).
Definition card_exp (A B: J) := |fspace A B|.
Notation   "A ^c B"          := (card_exp A B).
