Require Import Init.Init.
Require Import Relation.Relation.
Require Import Structure.Structure.
Require Import Nat.Inductive.
Require Import Nat.Nature.
Require Import Nat.Recursion.
Require Import Nat.Nat_arith.

(* Order *)
Definition nat_order := {x: ω ⨉ ω| ∃ m, ∃ n, x = ⟨m, n⟩ ∧ m ∈ n}.
Notation   "m <ₙ n"  := (m <[nat_order] n).
Notation   "m ≮ₙ n"  := (m ≮[nat_order] n).
Notation   "m ≤ₙ n"  := (m ≤[nat_order] n).
Notation   "m ≰ₙ n"  := (m ≰[nat_order] n).

Lemma nat_less_e: ∀ m, ∀ n, m <ₙ n → m ∈ n.
Proof.
  intros m n P1.
  destruct (sub_e _ _ _ P1) as [_ [m' [n' [P4 P5]]]].
  apply (eq_cr (λ x, x ∈ _) (opair_eq_el _ _ _ _ P4)).
  apply (eq_cr (λ x, _ ∈ x) (opair_eq_er _ _ _ _ P4)).
  apply P5.
Qed.

Lemma nat_less_i: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m ∈ n → m <ₙ n.
Proof.
  intros m n P1 P2 P3.
  apply sub_i.
  + apply (cp_i _ _ _ _ P1 P2).
  + exists m.
    exists n.
    apply (and_i (eq_r _) P3).
Qed.

Lemma suc_less_i: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m <ₙ n → S(m) <ₙ S(n).
Proof.
  intros m n P1 P2 P3.
  pose (λ k, ∀ p, p ∈ ω → p <ₙ k → S(p) <ₙ S(k)) as P.
  assert (P 𝟢) as I1.
  { intros m1 _ Q1.
    apply bot_e.
    apply (empty_i _ (nat_less_e _ _ Q1)). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 m2 Q3 Q4.
    destruct (suc_e _ _ (nat_less_e _ _ Q4)) as [Q5 | Q5].
    + apply (eq_cr (λ x, S(x) <ₙ _) Q5).
      apply (nat_less_i _ _ (suc_is_nat _ Q1) (suc_is_nat _ (suc_is_nat _ Q1))).
      apply suc_i1.
    + apply (nat_less_i _ _ (suc_is_nat _ Q3) (suc_is_nat _ (suc_is_nat _ Q1))).
      apply (nat_is_trans _ (suc_is_nat _ (suc_is_nat _ Q1)) _ (S(k))).
      - apply (nat_less_e _ _ (Q2 _ Q3 (nat_less_i _ _ Q3 Q1 Q5))).
      - apply suc_i1. }
  apply (induction_principle _ I1 I2 _ P2 _ P1 P3).
Qed.

Lemma nat_less_suc: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m <ₙ S(n) → m ≤ₙ n.
Proof.
  intros m n P1 P2 P3.
  pose (nat_less_e _ _ P3) as P4.
  destruct (suc_e _ _ P4) as [P5 | P5].
  + right.
    apply P5.
  + left.
    apply (nat_less_i _ _ P1 P2 P5).
Qed.

Lemma less_suc: ∀ m, m ∈ ω → m <ₙ S(m).
Proof.
  intros m P1.
  apply (nat_less_i _ _ P1 (suc_is_nat _ P1)).
  apply suc_i1.
Qed.

Lemma suc_le_nat: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m <ₙ n → S(m) ≤ₙ n.
Proof.
  intros m n P1 P2 P3.
  destruct (suc_e n (S(m))) as [P4 | P4].
  + apply nat_less_e.
    apply (suc_less_i _ _ P1 P2 P3).
  + right.
    apply P4.
  + left.
    apply (nat_less_i _ _ (suc_is_nat _ P1) P2 P4).
Qed.

Lemma suc_less_e: ∀ m, ∀ n, m ∈ ω → n ∈ ω → S(m) <ₙ S(n) → m <ₙ n.
Proof.
  intros m n P1 P2 P3.
  destruct (nat_less_suc _ _ (suc_is_nat _ P1) P2 P3) as [P4 | P4].
  + apply (nat_less_i _ _ P1 P2).
    apply (nat_is_trans _ P2 _ (S(m)) (suc_i1 _) (nat_less_e _ _ P4)).
  + apply (eq_cl (λ x, m <ₙ x) P4).
    apply (less_suc _ P1).
Qed.

Lemma nat_less_trans: r_trans nat_order ω.
Proof.
  intros m n p P1 P2 P3 P4 P5.
  pose (nat_less_e _ _ P4) as P6.
  pose (nat_less_e _ _ P5) as P7.
  apply (nat_less_i _ _  P1 P3).
  apply (nat_is_trans _ P3 _ _ P6 P7).
Qed.

Lemma nat_less_irrefl: r_irrefl nat_order ω.
Proof.
  intros n P1 P2.
  apply (nin_self n).
  apply (nat_less_e _ _ P2).
Qed.

Lemma nat_less_tricho_weak: tricho_weak nat_order ω.
Proof.
  intros m n P1 P2.
  pose (λ k, k ∈ ω → k <ₙ n ∨ k = n ∨ n <ₙ k) as P.
  assert (P 𝟢) as I1.
  { intros Q1.
    destruct (LEM (n = 𝟢)) as [Q2 | Q2].
    + right. left.
      apply (eq_s Q2).
    + left.
      apply (nat_less_i _ _ empty_is_nat P2 (empty_in_nat _ P2 Q2)). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 Q3.
    destruct (Q2 Q1) as [Q4 | [Q4 | Q4]].
    + destruct (suc_le_nat _ _ Q1 P2 Q4) as [Q5 | Q5].
      - left.
        apply Q5.
      - right. left.
        apply Q5.
    + right. right.
      apply (eq_cl (λ x, x <ₙ S(k)) Q4).
      apply (less_suc _ Q1).
    + right. right.
      apply (nat_less_i _ _ P2 Q3).
      apply (nat_is_trans _ Q3 _ _ (nat_less_e _ _ Q4) (suc_i1 _)). }
  apply (induction_principle _ I1 I2 _ P1 P1).
Qed.

Lemma nat_less_tricho: tricho nat_order ω.
Proof.
  apply weak_to_tricho.
  + apply nat_less_tricho_weak.
  + apply nat_less_irrefl.
  + apply nat_less_trans.
Qed.

Lemma empty_less: ∀ n, n ∈ ω → n ≠ 𝟢 → 𝟢 <ₙ n.
Proof.
  intros n P1 P2.
  apply (nat_less_i _ _ empty_is_nat P1).
  apply (empty_in_nat _ P1 P2).
Qed.

Lemma not_less_empty: ∀ n, n ∈ ω → n ≠ 𝟢 → n ≮ₙ 𝟢.
Proof.
  intros n P1 P2.
  destruct (nat_less_tricho _ _ empty_is_nat P1)
    as [[_ [_ Q1]] | [[_ [Q1 _]] | [Q1 _]]].
  + apply Q1.
  + apply bot_e.
    apply (P2 (eq_s Q1)).
  + apply bot_e.
    apply (Q1 (empty_less _ P1 P2)).
Qed.

Lemma nat_po: po nat_order ω.
Proof.
  split.
  + apply nat_less_trans.
  + apply nat_less_irrefl.
Qed.

Lemma nat_lo: lo nat_order ω.
Proof.
  split.
  + apply nat_less_trans.
  + apply nat_less_tricho.
Qed.

Lemma nat_less_least_prop: least_prop nat_order ω.
Proof.
  intros S P1 P2.
  apply nn_e.
  intros P3.
  (*pose (ω \ S) as K.*)
  pose (λ k, k ∈ ω → ∀ k', k' ∈ ω → k' <ₙ k → k' ∉ S) as P.
  assert (P 𝟢) as I1.
  { intros Q1 k' Q2 Q3 Q4.
    destruct (LEM (k' = 𝟢)) as [Q5 | Q5].
    + apply (nat_less_irrefl _ Q2).
      apply (eq_cr (λ x, k' <ₙ x) Q5 Q3).
    + apply (not_less_empty _ Q2 Q5 Q3). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 Q3 k' Q4 Q5 Q6.
    apply P3.
    exists k'.
    split.
    + apply Q6.
    + intros x Q7.
      apply (lo_nl_e _ _ _ _ nat_lo (P1 _ Q7) Q4).
      intros Q8.
      destruct (nat_less_suc _ _ Q4 Q1 Q5) as [Q9 | Q9].
      - apply (Q2 Q1 _ (P1 _ Q7)
          (l_l_t _ _ _ _ _ nat_less_trans (P1 _ Q7) Q4 Q1 Q8 Q9)).
        apply Q7.
      - apply (Q2 Q1 _ (P1 _ Q7) (eq_cl (λ y, x <ₙ y) Q9 Q8)).
        apply Q7. }
  apply P2.
  apply empty_unique.
  intros x P4.
  pose (P1 _ P4) as P5.
  apply (induction_principle _ I1 I2 _ (suc_is_nat _ P5)
    (suc_is_nat _ P5) _ P5 (less_suc _ P5)).
  apply P4.
Qed.

Lemma nat_wo: wo nat_order ω.
Proof.
  split.
  + apply nat_lo.
  + apply nat_less_least_prop.
Qed.

Lemma nat_l_l_t: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω → m <ₙ n → n <ₙ p
  → m <ₙ p.
Proof.
  intros m n p.
  apply (l_l_t _ _ _ _ _ nat_less_trans).
Qed.

Lemma nat_le_l_t: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω → m ≤ₙ n → n <ₙ p
  → m <ₙ p.
Proof.
  intros m n p.
  apply (le_l_t _ _ _ _ _ nat_less_trans).
Qed.

Lemma nat_l_le_t: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω → m <ₙ n → n ≤ₙ p
  → m <ₙ p.
Proof.
  intros m n p.
  apply (l_le_t _ _ _ _ _ nat_less_trans).
Qed.

Lemma nat_le_le_t: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω → m ≤ₙ n → n ≤ₙ p
  → m ≤ₙ p.
Proof.
  intros m n p.
  apply (le_le_t _ _ _ _ _ nat_less_trans).
Qed.
(*----------------------------------------------------------------------------*)

(* Arith *)
Lemma add_less: ∀ m, ∀ p, m ∈ ω → p ∈ ω → m <ₙ m +ₙ S(p).
Proof.
  intros m p P1 P2.
  apply (eq_cr (λ x, m <ₙ x) (add_red _ _ P1 P2)).
  pose (λ k, m <ₙ S(m +ₙ k)) as P.
  assert (P 𝟢) as I1.
  { red.
    apply (eq_cr (λ x, m <ₙ S(x)) (add_zero _ P1)).
    apply (less_suc _ P1). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2.
    pose (suc_is_nat _ (add_is_nat _ _ P1 Q1)) as Q3.
    apply (eq_cr (λ x, m <ₙ S(x)) (add_red _ _ P1 Q1)).
    apply (l_l_t _ _ _ _ _ nat_less_trans P1 Q3 (suc_is_nat _ Q3)).
    + apply Q2.
    + apply (less_suc _ Q3). }
  apply (induction_principle _ I1 I2 _ P2).
Qed.

Lemma add_le: ∀ m, ∀ p, m ∈ ω → p ∈ ω → m ≤ₙ m +ₙ p.
Proof.
  intros m p P1 P2.
  destruct (LEM (p = 𝟢)) as [P3|P3].
  + apply (eq_cr (λ x, m ≤ₙ(m +ₙ x)) P3).
    apply (eq_cr (λ x, m ≤ₙ x) (add_zero _ P1)). 
    right.
    apply eq_r.
  + destruct (nat_is_suc _ P2 P3) as [x [P4 P5]].
    apply (eq_cr (λ x, m ≤ₙ (m +ₙ x)) P5).
    left.
    apply (add_less _ _ P1 P4).
Qed.

Lemma ex_less: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω → m +ₙ S(p) = n → m <ₙ n.
Proof.
  intros m n p P1 P2 P3 P4.
  apply (eq_cl (λ x, m <ₙ x) P4).
  apply (add_less _ _ P1 P3).
Qed.

Lemma less_ex: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m <ₙ n → ∃ p, p ∈ ω ∧ m +ₙ S(p) = n.
Proof.
  intros m n P1 P2 P3.
  pose (λ k, k <ₙ m ∨ m = k ∨ ∃ p, p ∈ ω ∧ m +ₙ S(p) = k) as P.
  assert (P 𝟢) as I1.
  { destruct (LEM (m = 𝟢)) as [P4 | P4].
    + right. left.
      apply P4.
    + left.
      apply (empty_less _ P1 P4). }
  assert (induction_step P) as I2.
  { intros k Q1 [Q2 | [Q2 | Q2]].
    + destruct (suc_le_nat _ _ Q1 P1 Q2) as [Q3 | Q3].
      - left.
        apply Q3.
      - right. left.
        apply (eq_s Q3).
    + right. right.
      exists 𝟢.
      split.
      - apply empty_is_nat.
      - apply (eq_cr (λ x, x = _) (add_red _ _ P1 empty_is_nat)).
        apply (eq_cr (λ x, S(x) = _) (add_zero _ P1)).
        apply (eq_cr (λ x, S(x) = _) Q2).
        apply eq_r.
    + destruct Q2 as [p [Q3 Q4]].
      right. right.
      exists (S(p)).
      split.
      - apply (suc_is_nat _ Q3).
      - apply (eq_cr (λ x, x = S(k)) (add_red _ _ P1 (suc_is_nat _ Q3))).
        apply (eq_cr (λ x, S(x) = S(k)) Q4).
        apply eq_r. }
  destruct (induction_principle _ I1 I2 _ P2) as [P4 | [P4 | P4]].
  + apply bot_e.
    apply (nat_less_irrefl _ P1 (nat_l_l_t _ _ _ P1 P2 P1 P3 P4)).
  + apply bot_e.
    apply (nat_less_irrefl _ P1 (eq_cr (λ x, m <ₙ x) P4 P3)).
  + apply P4.
Qed.

Lemma less_add_cancel: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω
  → m +ₙ p <ₙ n +ₙ p → m <ₙ n.
Proof.
  intros m n p P1 P2 P3 P4.
  destruct (less_ex _ _ (add_is_nat _ _ P1 P3) (add_is_nat _ _ P2 P3) P4) 
    as [r [P5 P6]].
  apply (ex_less _ _ r P1 P2 P5).
  apply (add_cancel _ _ _ 
    (add_is_nat _ _ P1 (suc_is_nat _ P5)) P2 P3).
  apply (eq_t (add_132 _ _ _ P1 (suc_is_nat _ P5) P3) P6).
Qed.

Lemma less_add_eq_r: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω → m <ₙ n
  → m +ₙ p <ₙ n +ₙ p.
Proof.
  intros m n p P1 P2 P3 P4.
  pose (λ k, (m +ₙ k) <ₙ (n +ₙ k)) as P.
  assert (P 𝟢) as I1.
  { red.
    apply (eq_cr (λ x, x <ₙ (n +ₙ 𝟢)) (add_zero _ P1)).
    apply (eq_cr (λ x, m <ₙ x) (add_zero _ P2)).
    apply P4. }
  assert (induction_step P) as I2.
  { intros k Q1 Q2.
    red.
    apply (eq_cr (λ x, x <ₙ (n +ₙ S(k))) (add_red _ _ P1 Q1)).
    apply (eq_cr (λ x, S(m +ₙ k) <ₙ x) (add_red _ _ P2 Q1)).
    apply (suc_less_i _ _ (add_is_nat _ _ P1 Q1) (add_is_nat _ _ P2 Q1)).
    apply Q2. }
  apply (induction_principle _ I1 I2 _ P3).
Qed.

Lemma less_add_eq_l: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω → m <ₙ n
  → p +ₙ m <ₙ p +ₙ n.
Proof.
  intros m n p P1 P2 P3 P4.
  apply (eq_cr (λ x, x <ₙ _) (add_commu _ _ P3 P1)).
  apply (eq_cr (λ x, _ <ₙ x) (add_commu _ _ P3 P2)).
  apply (less_add_eq_r _ _ _ P1 P2 P3 P4).
Qed.

Lemma less_add_preserve: ∀ m, ∀ n, ∀ p, ∀ q, m ∈ ω → n ∈ ω → p ∈ ω → q ∈ ω
  → m <ₙ n → p <ₙ q → m +ₙ p <ₙ n +ₙ q.
Proof.
  intros m n p q P1 P2 P3 P4 P5 P6.
  pose (less_add_eq_r _ _ _ P1 P2 P3 P5) as P7.
  pose (less_add_eq_l _ _ _ P3 P4 P2 P6) as P8.
  apply (nat_l_l_t _ (n +ₙ p)).
  all: is_nat.
Qed.

Lemma mul_less: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω → m <ₙ n → 𝟢 <ₙ p
  → m ×ₙ p <ₙ n ×ₙ p.
Proof.
  intros m n p P1 P2 P3 P4 P5.
  pose (λ k, k = 𝟢 ∨ m ×ₙ k <ₙ n ×ₙ k) as P.
  assert (P 𝟢) as I1.
  { left.
    apply eq_r. }
  assert (induction_step P) as I2.
  { intros k Q1 [Q2 | Q2].
    + right.
      apply (eq_cr (λ k, _ ×ₙ S(k) <ₙ _ ×ₙ S(k)) Q2).
      apply (eq_cr (λ x, x <ₙ _) (mul_one _ P1)).
      apply (eq_cr (λ x, _ <ₙ x) (mul_one _ P2)).
      apply P4.
    + right.
      apply (eq_cr (λ x, x <ₙ _) (mul_red _ _ P1 Q1)).
      apply (eq_cr (λ x, _ <ₙ x) (mul_red _ _ P2 Q1)).
      apply less_add_preserve.
      all: is_nat. }
  destruct (induction_principle _ I1 I2 _ P3) as [P6 | P6].
  + apply bot_e.
    apply (nat_less_irrefl _ P3).
    apply (eq_cr (λ x, x <ₙ _) P6 P5).
  + apply P6.
Qed.

(*Lemma less_nat_preserve: ∀ m, ∀ n, m ∈ ω → n < ω → 𝟢 < m → 𝟢 < n → 0 < m ×ₙ m.*)
(*Lemma mul_order_l: ∀ m, ∀ n, ∀ p, ∀ q, m ∈ ω → n ∈ ω → p ∈ ω → q ∈ ω →*)
  (*m <ₙ n → p <ₙ q → m ×ₙ q +ₙ n ×ₙ p <ₙ m ×ₙ p +ₙ n ×ₙ q.*)
(*Proof.*)
  (*intros m n p q P1 P2 P3 P4 P5 P6.*)
  (*destruct (less_ex _ _ P1 P2 P5) as [s1 [P7 P8]].*)
  (*destruct (less_ex _ _ P3 P4 P6) as [s2 [P9 P10]].*)
  (*apply (eq_cl (λ x, _ ×ₙ x +ₙ _ <ₙ _ +ₙ n ×ₙ x) P10).*)
  (*apply (eq_cr (λ x, x +ₙ _ <ₙ _) (distr_l _ _ _ P1 P3 (suc_is_nat _ P9))).*)
  (*apply (eq_cr (λ x, _ <ₙ _ +ₙ x) (distr_l _ _ _ P2 P3 (suc_is_nat _ P9))).*)
  (*apply (eq_cl (λ x, x <ₙ _) (add_assoc _ _ _ (mul_is_nat _ _ P1 P3)*)
    (*(mul_is_nat _ _ P1 (suc_is_nat _ P9)) (mul_is_nat _ _ P2 P3))).*)
  (*apply (less_add_eq_l).*)
  (*all: is_nat.*)
  (*apply (eq_cr (λ x, x <ₙ _) (add_commu _ _*)
    (*(mul_is_nat _ _ P1 (suc_is_nat _ P9)) (mul_is_nat _ _ P2 P3))).*)
  (*apply (less_add_eq_l).*)
  (*all: is_nat.*)
  (*apply (eq_cl (λ x, _ <ₙ x ×ₙ _) P8).*)
  (*apply (eq_cr (λ x, _ <ₙ x) (distr_r _ _ _ P1 (suc_is_nat _ P7)*)
    (*(suc_is_nat _ P9))).*)
  (*apply (eq_cl (λ x, x <ₙ _) (add_zero _ (mul_is_nat _ _ P1 (suc_is_nat _ P9)))).*)
  (*apply (less_add_eq_l).*)
  (*all: is_nat.*)
  (*destruct (nat_less_tricho_weak _ _ empty_is_nat (mul_is_nat _ _ (suc_is_nat _ P7) (suc_is_nat _ P9))) as [Q1 | [Q1 | Q1]].*)
  (*+ apply Q1.*)
  (*+ destruct (mul_eq_zero _ _ (suc_is_nat _ P7) (suc_is_nat _ P9) (eq_s Q1)) as [Q2 | Q2].*)
    (*- *)


  (*rewrite <- P10.*)
  (*rewrite (distributive_l (m +ₙ S(s1)) p (S(s2))).*)
  (*rewrite (distributive_l m p (S(s2))).*)
  (*rewrite (distributive_r m (S(s1)) p).*)
  (*rewrite (distributive_r m (S(s1)) (S(s2))).*)
  (*rewrite (add_associative (m ×ₙ p +ₙ S( s1) ×ₙ p) (m ×ₙ S( s2)) (S( s1) ×ₙ S( s2))).*)
  (*rewrite (add_commutative (m ×ₙ p +ₙ S( s1) ×ₙ p) (m ×ₙ S( s2))).*)
  (*rewrite (add_associative (m ×ₙ p)*)
    (*(m ×ₙ S( s2) +ₙ (m ×ₙ p +ₙ S( s1) ×ₙ p)) (S( s1) ×ₙ S( s2))).*)
  (*rewrite (add_associative (m ×ₙ p) (m ×ₙ S( s2)) (m ×ₙ p +ₙ S( s1) ×ₙ p)).*)
  (*rewrite (multi_red _ _ (suc_is_nat _ P7) P9).*)
  (*rewrite (add_associative ((m ×ₙ p +ₙ m ×ₙ S( s2)) +ₙ (m ×ₙ p +ₙ S( s1) ×ₙ p))*)
    (*(S(s1)) (S(s1) ×ₙ s2)).*)
  (*apply (less_le_less _ *)
    (*(((m ×ₙ p +ₙ m ×ₙ S( s2)) +ₙ (m ×ₙ p +ₙ S( s1) ×ₙ p)) +ₙ S( s1)) _).*)
  (*all: is_nat.*)
  (*apply add_less.*)
  (*all: is_nat.*)
  (*apply add_less_equal.*)
  (*all: is_nat.*)
(*Qed.*)


(*Lemma less_multi_eq: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω -> m <ₙ n ->*)
  (*(m ×ₙ S(p)) <ₙ (n ×ₙ S(p)).*)
(*Proof.*)
  (*intros m n p P1 P2 P3 P4.*)
  (*pose (fun k => (m ×ₙ S(k)) <ₙ (n ×ₙ S(k))) as P.*)
  (*assert (P 𝟢) as I1.*)
  (*{ red. *)
    (*rewrite (multi_one _ P1).*)
    (*rewrite (multi_one _ P2).*)
    (*apply P4. }*)
  (*assert (induction_step P) as I2.*)
  (*{ intros k Q1 Q2.*)
    (*red.*)
    (*rewrite (multi_red _ _ P1 (suc_is_nat _ Q1)).*)
    (*rewrite (multi_red _ _ P2 (suc_is_nat _ Q1)).*)
    (*apply (less_add_less m n (m ×ₙ S(k)) (n ×ₙ S(k))).*)
    (*all: is_nat. }*)
  (*apply (induction_principle _ I1 I2 _ P3).*)
(*Qed.*)

(*Lemma equal_less_less: forall m n p q, m ∈ ω -> n ∈ ω -> p ∈ ω -> q ∈ ω ->*)
  (*(m +ₙ p) = (n +ₙ q) -> m <ₙ n -> q <ₙ p.*)
(*Proof.*)
  (*intros m n p q P1 P2 P3 P4 P5 P6.*)
  (*destruct (less_ex _ _ P1 P2 P6) as [r [P7 P8]].*)
  (*rewrite <- P8 in P5.*)
  (*rewrite (add_commutative _ _ P1 P3) in P5.*)
  (*rewrite (add_commutative _ _ P1 (suc_is_nat _ P7)) in P5.*)
  (*rewrite (add_cyc _ _ _ (suc_is_nat _ P7) P1 P4) in P5.*)
  (*rewrite (add_commutative _ _ (suc_is_nat _ P7) P4) in P5.*)
  (*symmetry in P5.*)
  (*apply (ex_less _ _ r P4 P3 P7).*)
  (*apply (add_cancellation _ _ _ *)
    (*(add_is_nat _ _ P4 (suc_is_nat _ P7)) P3 P1 P5).*)
(*Qed.*)

(*Lemma less_multi_cancellation: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω -> *)
  (*(m ×ₙ S(p)) <ₙ (n ×ₙ S(p)) -> m <ₙ n.*)
(*Proof.*)
  (*intros m n p P1 P2 P3 P4.*)
  (*destruct (nat_trichotomy _ _ P1 P2) as [[P5 _] | [[_ [P5 _]] | [_ [_ P5]]]].*)
  (*+ apply P5.*)
  (*+ rewrite P5 in P4.*)
    (*pose (nat_not_in_self _ (multi_is_nat _ _ P2 (suc_is_nat _ P3))) as P6.*)
    (*contradiction.*)
  (*+ pose (less_multi_eq _ _ _ P2 P1 P3 P5) as P6.*)
    (*absurd (m ×ₙ S( p) <ₙ m ×ₙ S( p)).*)
    (*- apply nat_not_in_self.*)
      (*is_nat.*)
    (*- apply (less_less_less _ (n ×ₙ S(p)) _).*)
      (*all: is_nat.*)
(*Qed.*)

(*Lemma not_equal_less: forall m n, m ∈ ω -> n ∈ ω -> m <> n -> *)
  (*m <ₙ n \/ n <ₙ m.*)
(*Proof.*)
  (*intros m n P1 P2 P3.*)
  (*destruct (nat_trichotomy _ _ P1 P2) as [P4|[P4|P4]].*)
  (*+ destruct P4 as [P4 _].*)
    (*left. *)
    (*apply P4.*)
  (*+ destruct P4 as [_ [P4 _]].*)
    (*contradiction.*)
  (*+ destruct P4 as [_ [_ P4]].*)
    (*right.*)
    (*apply P4.*)
(*Qed.*)

(*Lemma less_not_equal_1: forall m n, m ∈ ω -> n ∈ ω -> m <ₙ n ->*)
  (*m <> n.*)
(*Proof.*)
  (*intros m n P1 P2 P3.*)
  (*destruct (nat_trichotomy _ _ P1 P2) as [P4|[P4|P4]].*)
  (*+ destruct P4 as [_ [P4 _]].*)
    (*apply P4.*)
  (*+ destruct P4 as [P4 _].*)
    (*contradiction.*)
  (*+ destruct P4 as [_ [P4 _]].*)
    (*apply P4.*)
(*Qed.*)

(*Lemma less_not_equal_2: forall m n, m ∈ ω -> n ∈ ω -> m <ₙ n ->*)
  (*n <> m.*)
(*Proof.*)
  (*intros m n P1 P2 P3 P4.*)
  (*symmetry in P4.*)
  (*apply (less_not_equal_1 _ _ P1 P2 P3 P4).*)
(*Qed.*)

(*Lemma multi_cancellation: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->*)
  (*m ×ₙ S(p) = n ×ₙ S(p) -> m = n.*)
(*Proof.*)
  (*intros m n p P1 P2 P3 P4.*)
  (*destruct (nat_trichotomy _ _ P1 P2) as [[P5 _] | [[_ [P5 _]] | [_ [_ P5]]]].*)
  (*+ absurd (m ×ₙ S(p) = n ×ₙ S(p)).*)
    (*- apply less_not_equal_1.*)
      (*all: is_nat.*)
      (*apply (less_multi_eq _ _ p P1 P2 P3 P5).*)
    (*- apply P4.*)
  (*+ apply P5.*)
  (*+ absurd (m ×ₙ S(p) = n ×ₙ S(p)).*)
    (*- apply less_not_equal_2.*)
      (*all: is_nat.*)
      (*apply (less_multi_eq _ _ p P2 P1 P3 P5).*)
    (*- apply P4.*)
(*Qed.*)

(*Lemma not_equal_cyc_equal: forall m n p q, m ∈ ω -> n ∈ ω -> p ∈ ω -> q ∈ ω ->*)
  (*p <> q -> m ×ₙ p +ₙ n ×ₙ q = m ×ₙ q +ₙ n ×ₙ p -> m = n.*)
(*Proof.*)
  (*intros m n p q P1 P2 P3 P4 P5 P6.*)
  (*destruct (not_equal_less _ _ P3 P4 P5) as [P7|P7].*)
  (*+ destruct (less_ex _ _ P3 P4 P7) as [x [P8 P9]].*)
    (*rewrite <- P9 in P6.*)
    (*rewrite (distributive_l n p (S(x))) in P6.*)
    (*rewrite (add_associative (m ×ₙ p) (n ×ₙ p) (n ×ₙ S( x))) in P6.*)
    (*rewrite (add_commutative (m ×ₙ p +ₙ n ×ₙ p) (n ×ₙ S( x))) in P6.*)
    (*rewrite (distributive_l m p (S(x))) in P6.*)
    (*rewrite (add_cyc (m ×ₙ p) (m ×ₙ S( x)) (n ×ₙ p)) in P6.*)
    (*rewrite (add_commutative (m ×ₙ p +ₙ n ×ₙ p) (m ×ₙ S( x))) in P6.*)
    (*assert (n ×ₙ S( x) = m ×ₙ S( x)) as P10.*)
    (*{ apply (add_cancellation _ _ (m ×ₙ p +ₙ n ×ₙ p)).*)
      (*all: is_nat. }*)
    (*symmetry.*)
    (*apply (multi_cancellation _ _ x).*)
    (*all: is_nat.*)
  (*+ destruct (less_ex _ _ P4 P3 P7) as [x [P8 P9]].*)
    (*rewrite <- P9 in P6.*)
    (*rewrite (distributive_l m q (S(x))) in P6.*)
    (*rewrite (add_cyc (m ×ₙ q) (m ×ₙ S(x)) (n ×ₙ q)) in P6.*)
    (*rewrite (add_commutative (m ×ₙ q +ₙ n ×ₙ q) (m ×ₙ S(x))) in P6.*)
    (*rewrite (distributive_l n q (S(x))) in P6.*)
    (*rewrite (add_associative (m ×ₙ q) (n ×ₙ q) (n ×ₙ S( x))) in P6.*)
    (*rewrite (add_commutative (m ×ₙ q +ₙ n ×ₙ q) (n ×ₙ S( x))) in P6.*)
    (*assert (m ×ₙ S( x) = n ×ₙ S( x)) as P10.*)
    (*{ apply (add_cancellation _ _ (m ×ₙ q +ₙ n ×ₙ q)).*)
      (*all: is_nat. }*)
    (*apply (multi_cancellation _ _ x).*)
    (*all: is_nat.*)
(*Qed.*)
(*----------------------------------------------------------------------------*)
