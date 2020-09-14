Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Nat.
Require Import Ordinal.Order.
Require Import Ordinal.Transfinite.
Require Import Ordinal.Epsilon.

Require dpdgraph.dpdgraph.

(* Ordinal Number *)
Definition Ord (x: J) := ∃ R, ∃ A, wo R A ∧ x = EI(R, A).

Lemma ord_i: ∀ O, trans O → wo (ER(O)) O → Ord O.
Proof.
  intros O P1 P2.
  exists (ER(O)).
  exists O.
  split.
  + apply P2.
  + apply (eq_s (eps_image_self _ P1 P2)).
Qed.

Lemma ord_e: ∀ O, Ord O → ∃ R, ∃ A, wo R A ∧ O = EI(R, A).
Proof.
  intros O P1.
  apply P1.
Qed.

Lemma ord_wo: ∀ O, Ord O → wo (ER(O)) O.
Proof.
  intros O P1.
  destruct (ord_e _ P1) as [R [A [P2 P3]]].
  apply (eq_cr (λ x, wo(ER(x)) x) P3).
  apply (wo_eps_image _ _ P2).
Qed.

Lemma ord_trans: ∀ O, Ord O → trans O.
Proof.
  intros O P1.
  destruct (ord_e _ P1) as [R [A [P2 P3]]].
  apply (eq_cr (λ x, trans x) P3).
  apply (eps_image_t _ _ P2).
Qed.

Lemma ord_e2: ∀ O, Ord O → O = EI(ER(O), O).
Proof.
  intros O P1.
  apply eq_s.
  apply eps_image_self.
  + apply (ord_trans _ P1).
  + apply (ord_wo _ P1).
Qed.

Lemma in_ord_ord: ∀ O, ∀ a, Ord O → a ∈ O → Ord a.
Proof.
  intros O a P1 P2.
  pose (ord_wo _ P1) as P3.
  pose (ord_trans _ P1) as P4.
  apply ord_i.
  + destruct (ord_e _ P1) as [R [A [P5 P6]]].
    pose (eq_cl (λ x, a ∈ x) P6 P2) as P7.
    destruct (eps_image_e _ _ _ P5 P7) as [s [P8 P9]].
    apply (eq_cr (λ x, trans x) P9).
    apply (eps_trans _ _ _ P5 P8).
  + pose (sub_wo _ _ _ P3 (trans_e2 _ P4 _ P2)) as P5.
    pose (eps_rel_eq _ _ (trans_e2 _ P4 _ P2)) as P6.
    apply (wo_rel_exten _ _ _ P6 P5).
Qed.

(*Lemma ord_suc_ord: ∀ O, Ord O → Ord (S(O)).*)
(*Proof.*)
  (*intros O P1.*)
  (*apply ord_i.*)
  (*+ apply (suc_trans _ (ord_trans _ P1)).*)
  (*+ pose wo_i. intros s.*)

Lemma ord_nin_self: ∀ O, Ord O → O ∉ O.
Proof.
  intros O P1.
  apply nin_self.
Qed.

Lemma ord_inter2_ord: ∀ A, ∀ B, Ord A → Ord B → Ord (A ∩ B).
Proof.
  intros A B P1 P2.
  pose (ord_wo _ P1) as P3.
  pose (ord_wo _ P2) as P4.
  pose (ord_trans _ P1) as P5.
  pose (ord_trans _ P2) as P6.
  pose (inter2_sub_l A B) as P7.
  pose (inter2_sub_r A B) as P8.
  apply ord_i.
  + intros x t Q1 Q2.
    destruct (inter2_e _ _ _ Q2) as [Q3 Q4].
    apply inter2_i.
    - pose (eq_cr (λ t, x ∈ t) (seg_eps_rel_trans _ _ P5 Q3) Q1) as Q5.
      apply (seg_e1 _ _ _ _ Q3 Q5).
    - pose (eq_cr (λ t, x ∈ t) (seg_eps_rel_trans _ _ P6 Q4) Q1) as Q5.
      apply (seg_e1 _ _ _ _ Q4 Q5).
  + pose (sub_wo _ _ _ P3 P7) as Q1.
    pose (eps_rel_eq _ _ P7) as Q2.
    apply (wo_rel_exten _ _ _ Q2 Q1).
Qed.

Lemma ord_inter_ord: ∀ A, A ≠ ∅ → (∀ a, a ∈ A → Ord a) → Ord (∩A).
Proof.
  intros A P1 P2.
  apply ord_i.
  + intros x t Q1 Q2.
    apply inter_i.
    - apply P1.
    - intros a Q3.
      pose (inter_e _ _ Q2 _ Q3) as Q4.
      pose (ord_trans _ (P2 _ Q3)) as Q5.
      pose (eq_cr (λ t, x ∈ t) (seg_eps_rel_trans _ _ Q5 Q4) Q1) as Q6.
      apply (seg_e1 _ _ _ _ Q4 Q6).
  + destruct (nempty_ex _ P1) as [a Q1].
    pose (inter_sub _ _ Q1) as Q2.
    pose (sub_wo _ _ _ (ord_wo _ (P2 _ Q1)) Q2) as Q3.
    pose (eps_rel_eq _ _ Q2) as Q4.
    apply (wo_rel_exten _ _ _ Q4 Q3).
Qed.

Lemma ord_in_psub: ∀ A, ∀ B, Ord A → Ord B → A ∈ B → A ⊂ B.
Proof.
  intros A B P1 P2 P3.
  apply psub_i.
  + apply trans_e2.
    - apply (ord_trans _ P2).
    - apply P3.
  + intros P4.
    apply (nin_self A).
    apply (eq_cr (λ x, A ∈ x) P4).
    apply P3.
Qed.

Lemma ord_psub_in: ∀ A, ∀ B, Ord A → Ord B → A ⊂ B → A ∈ B.
Proof.
  intros A B P1 P2 P3.
  pose (ord_wo _ P2) as P4.
  pose (ord_trans _ P2) as P5.
  pose (ord_trans _ P1) as P6.
  apply (eq_cr (λ x, A ∈ x) (ord_e2 _ P2)).
  destruct (psub_e2 _ _ P3) as [xx [P7 P8]].
  destruct (wo_prop_least (λ x, x ∉ A) _ _ _ P4 P8 P7)
    as [x0 [P9 [P10 P11]]].
  pose (psub_e _ _ P3) as P12.
  apply ran_i.
  exists x0.
  apply (fval_e).
  + apply sub_a.
    split.
    - intros x Q1.
      apply (eq_cr (λ y, x ∈ y) (eps_self _ _ P5 P4 P9)).
      pose (P12 _ Q1) as Q2.
      destruct (wo_tricho_weak _ _ P4 _ _ (P12 _ Q1) P9) as [Q3 | [Q3 | Q3]].
      * apply (eps_rel_e _ _ _ Q3).
      * apply bot_e.
        apply P10.
        apply (eq_cl (λ x, x ∈ A) Q3).
        apply Q1.
      * pose (eps_rel_e _ _ _ Q3) as Q4.
        pose (seg_eps_rel_trans _ _ P6 Q1) as Q5.
        pose (eq_cr (λ x, x0 ∈ x) Q5 Q4) as Q6.
        apply bot_e.
        apply P10.
        apply (seg_e1 _ _ _ _ Q1 Q6).
    - intros x Q1.
      pose (eq_cl (λ y, x ∈ y) (eps_self _ _ P5 P4 P9) Q1) as Q2.
      pose (P5 _ _ Q2 P9) as Q3.
      apply (contraposition2 (P11 _ Q3)).
      apply (wo_nle_i _ _ _ _ P4 Q3 P9).
      apply (eps_rel_i _ _ _ Q3 P9 Q2). 
  + apply (eps_fn _ _ (ord_wo _ P2)).
  + apply (eq_cr (λ y, x0 ∈ y) (eps_dom _ _ (ord_wo _ P2))).
    apply P9.
Qed.

Lemma ord_ord_sub: ∀ A, ∀ B, Ord A → Ord B → A ⊆ B ∨ B ⊆ A.
Proof.
  intros A B P1 P2.
  apply nn_e.
  intros P3.
  destruct (not_or_and P3) as [P4 P5].
  apply (nin_self (A ∩ B)).
  apply inter2_i.
  + apply (ord_psub_in _ _ (ord_inter2_ord _ _ P1 P2) P1).
    apply psub_i.
    - apply inter2_sub_l.
    - intros Q1.
      apply bot_e.
      apply P4.
      apply (inter2_eq_sub_l _ _ Q1).
  + apply (ord_psub_in _ _ (ord_inter2_ord _ _ P1 P2) P2).
    apply psub_i.
    - apply inter2_sub_r.
    - intros Q1.
      apply bot_e.
      apply P5.
      apply (inter2_eq_sub_r _ _ Q1).
Qed.

Lemma ord_t: ∀ A, ∀ B, ∀ C, Ord A → Ord B → Ord C → A ∈ B → B ∈ C → A ∈ C.
Proof.
  intros A B C P1 P2 P3 P4 P5.
  apply (ord_psub_in _ _ P1 P3).
  apply (psub_t _ B _).
  + apply (ord_in_psub _ _ P1 P2 P4).
  + apply (ord_in_psub _ _ P2 P3 P5).
Qed.

Lemma ord_tricho_weak: ∀ A, ∀ B, Ord A → Ord B → (A ∈ B) ∨ (A = B) ∨ (B ∈ A).
Proof.
  intros A B P1 P2.
  destruct (ord_ord_sub _ _ P1 P2) as [P3 | P3].
  + destruct (sub_e2 _ _ P3) as [P4 | P4].
    - left.
      apply (ord_psub_in _ _ P1 P2 P4).
    - right. left.
      apply P4.
  + destruct (sub_e2 _ _ P3) as [P4 | P4].
    - right. right.
      apply (ord_psub_in _ _ P2 P1 P4).
    - right. left.
      apply (eq_s P4).
Qed.

Lemma ord_tricho: ∀ A, ∀ B, Ord A → Ord B → 
  ((A ∈ B) ∧ (A ≠ B) ∧ (B ∉ A)) ∨ 
  ((A ∉ B) ∧ (A = B) ∧ (B ∉ A)) ∨ 
  ((A ∉ B) ∧ (A ≠ B) ∧ (B ∈ A)).
Proof.
  intros A B P1 P2.
  destruct (ord_tricho_weak _ _ P1 P2) as [P3 | [P3 | P3]].
  + left. repeat split.
    - apply P3.
    - intros P4.
      apply bot_e.
      apply (nin_self A).
      apply (eq_cr (λ x, A ∈ x) P4 P3).
    - intros P4.
      apply (nin_self A).
      apply (ord_t _ _ _ P1 P2 P1 P3 P4).
  + right. left. repeat split.
    - intros P4.
      apply (nin_self A).
      apply (eq_cr (λ x, A ∈ x) P3 P4).
    - apply P3.
    - intros P4.
      apply (nin_self A).
      apply (eq_cr (λ x, x ∈ A) P3 P4).
  + right. right. repeat split.
    - intros P4.
      apply (nin_self A).
      apply (ord_t _ _ _ P1 P2 P1 P4 P3).
    - intros P4.
      apply bot_e.
      apply (nin_self A).
      apply (eq_cr (λ x, x ∈ A) P4 P3).
    - apply P3.
Qed.

Lemma ord_inter2_eq: ∀ A, ∀ B, Ord A → Ord B → A ∩ B = A ∨ A ∩ B = B.
Proof.
  intros A B P1 P2.
  destruct (ord_ord_sub _ _ P1 P2) as [P3 | P3].
  + left.
    apply (inter2_absorb_l _ _ P3).
  + right.
    apply (inter2_absorb_r _ _ P3).
Qed.

Lemma ord_least_bound: ∀ A, A ≠ ∅ → (∀ a, a ∈ A → Ord a) 
  → least_bound (ER(A)) A.
Proof.
  intros A P1 P2.
  destruct (nempty_ex _ P1) as [a0 P3].
  destruct (LEM (a0 ∩ A = ∅)) as [P4 | P4].
  + exists a0.
    split.
    - apply P3.
    - intros x P5.
      destruct (ord_tricho_weak _ _ (P2 _ P5) (P2 _ P3)) as [P6 | [P6 | P6]].
      * apply bot_e.
        apply (empty_i x).
        apply (eq_cl (λ y, x ∈ y) P4).
        apply (inter2_i _ _ _ P6 P5).
      * right.
        apply (eq_s P6).
      * left.
        apply (eps_rel_i _ _ _ P3 P5 P6).
  + pose (ord_wo _ (P2 _ P3)) as P5.
    pose (inter2_sub_l a0 A) as P6.
    destruct (wo_least_prop _ _ P5 _ P6 P4) as [a [P7 P8]].
    destruct (inter2_e _ _ _ P7) as [P9 P10].
    exists a.
    split.
    - apply P10.
    - intros x Q1.
      destruct (ord_tricho_weak _ _ (P2 _ Q1) (P2 _ P3)) as [Q2 | [Q2 | Q2]].
      * destruct (P8 _ (inter2_i _ _ _ Q2 Q1)) as [Q3 | Q3].
        ++left.
          apply (eps_rel_i _ _ _ P10 Q1 (eps_rel_e _ _ _ Q3)).
        ++right.
          apply Q3.
      * left.
        apply (eq_cr (λ x, a <[ER(A)] x) Q2).
        apply (eps_rel_i _ _ _ P10 P3 P9).
      * left.
        apply (eps_rel_i _ _ _ P10 Q1).
        apply (ord_t _ _ _ (P2 _ P10) (P2 _ P3) (P2 _ Q1) P9 Q2).
Qed.

Lemma empty_ord: Ord ∅.
Proof.
  apply ord_i.
  + apply empty_is_trans.
  + repeat split.
    - intros x y z P1.
      apply bot_e.
      apply (empty_i _ P1).
    - intros x y P1.
      apply bot_e.
      apply (empty_i _ P1).
    - intros S P1 P2.
      apply bot_e.
      apply P2.
      apply (sub_empty_empty _ P1).
Qed.

Lemma trans_ord_ord: ∀ A, trans A → (∀ a, a ∈ A → Ord a) → Ord A.
Proof.
  intros A P1 P2.
  apply ord_i.
  + apply P1.
  + repeat split.
    - intros x y z Q1 Q2 Q3 Q4 Q5.
      pose (eps_rel_e _ _ _ Q4) as Q6.
      pose (eps_rel_e _ _ _ Q5) as Q7.
      apply (eps_rel_i _ _ _ Q1 Q3).
      apply (ord_t _ _ _ (P2 _ Q1) (P2 _ Q2) (P2 _ Q3) Q6 Q7).
    - intros x y Q1 Q2.
      destruct (ord_tricho _ _ (P2 _ Q1) (P2 _ Q2))
        as [[Q3 [Q4 Q5]] | [[Q3 [Q4 Q5]] | [Q3 [Q4 Q5]]]].
      * left. repeat split.
        ++apply (eps_rel_i _ _ _ Q1 Q2 Q3).
        ++apply Q4.
        ++intros Q6.
          apply Q5.
          apply (eps_rel_e _ _ _ Q6).
      * right. left. repeat split.
        ++intros Q6.
          apply Q3.
          apply (eps_rel_e _ _ _ Q6).
        ++apply Q4.
        ++intros Q6.
          apply Q5.
          apply (eps_rel_e _ _ _ Q6).
      * right. right. repeat split.
        ++intros Q6.
          apply Q3.
          apply (eps_rel_e _ _ _ Q6).
        ++apply Q4.
        ++apply (eps_rel_i _ _ _ Q2 Q1 Q5).
    - intros S Q1 Q2.
      assert (∀ s, s ∈ S → Ord s) as Q3.
      { intros s Q3.
        apply (P2 _ (Q1 _ Q3)). }
      destruct (ord_least_bound _ Q2 Q3) as [s [Q4 Q5]].
      exists s.
      split.
      * apply Q4.
      * intros x Q6.
        destruct (Q5 _ Q6) as [Q7 | Q7].
        ++left.
          apply (eps_rel_i _ _ _ (Q1 _ Q4) (Q1 _ Q6)).
          apply (eps_rel_e _ _ _ Q7).
        ++right.
          apply Q7.
Qed.

(* Burali-Forti *)
Theorem no_ord_set: ~∃ A, ∀ a, Ord a ↔ a ∈ A.
Proof.
  intros [A P1].
  apply (nin_self A).
  apply P1.
  apply trans_ord_ord.
  + intros x a P2 P3.
    apply P1.
    apply (in_ord_ord a).
    - apply P1.
      apply P3.
    - apply P2.
  + intros a P2.
    destruct (P1 a) as [_ P3].
    apply (P3 P2).
Qed.

