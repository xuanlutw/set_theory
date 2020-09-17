Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Inductive.
Require Import Nat.Nature.
Require Import Nat.Recursion.
Require Import Nat.Nat_arith.

(* Order *)
Definition less (m n: J)    := m ∈ n.
Notation   "m <ₙ n"         := (less m n).
Definition less_eq (m n: J) := (less m n) ∨ (m = n).
Notation   "m ≤ₙ n"         := (less_eq m n).

Lemma in_suc: ∀ m, ∀ n, m <ₙ S(n) → m <ₙ n ∨ m = n.
Proof.
  intros m n P1.
  destruct (union2_e _ _ _ P1) as [P2 | P2].
  + left.
    apply P2.
  + right.
    apply eq_s.
    apply (sing_e _ _ P2).
Qed.

Lemma in_nat_nat: ∀ m, ∀ n, n ∈ ω → m <ₙ n → m ∈ ω.
Proof.
  intros m n P1 P2.
  pose (λ k, ∀ p, p ∈ k → p ∈ ω) as P.
  assert (P 𝟢) as I1.
  { intros m1 Q1.
    apply bot_e.
    apply (empty_i _ Q1). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 m1 Q3.
    destruct (in_suc _ _ Q3) as [Q4 | Q4].
    + apply (Q2 _ Q4).
    + apply (eq_cr (λ x, x ∈ ω) Q4).
      apply Q1. }
  apply (induction_principle _ I1 I2 _ P1 _ P2).
Qed.

Lemma suc_less: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m <ₙ n → S(m) <ₙ S(n).
Proof.
  intros m n P1 P2 P3.
  pose (λ k, ∀ p, p <ₙ k → S(p) <ₙ S(k)) as P.
  assert (P 𝟢) as I1.
  { intros m1 Q1.
    apply bot_e.
    apply (empty_i _ Q1). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 m2 Q3.
    destruct (in_suc _ _ Q3) as [Q4 | Q4].
    + pose (nat_is_trans _ (suc_is_nat _ (suc_is_nat _ Q1))) as Q5.
      apply (Q5 _ _ (Q2 _ Q4) (suc_i1 (S(k)))).
    + apply (eq_cr (λ x, S(x) ∈ S(S(k))) Q4).
      apply suc_i1. }
  apply (induction_principle _ I1 I2 _ P2 _ P3).
Qed.

Lemma suc_eq_or_less: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m <ₙ n → S(m) <ₙ n ∨ S(m) = n.
Proof.
  intros m n P1 P2 P3.
  apply (in_suc (S(m)) n).
  apply (suc_less _ _ P1 P2 P3).
Qed.

Lemma empty_in_nat: ∀ n, n ∈ ω → n ≠ 𝟢 → 𝟢 ∈ n.
Proof.
  intros n P1 P2.
  pose (λ k, k ∈ ω → k ≠ 𝟢 → 𝟢 ∈ k) as P.
  assert (P 𝟢) as I1.
  { intros Q1 Q2.
    apply bot_e.
    apply (Q2 (eq_r _)). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 Q3 Q4.
    destruct (LEM (k = 𝟢)) as [Q5 | Q5].
    + apply (eq_cr (λ x, 𝟢 ∈ S(x)) Q5).
      apply suc_i1.
    + pose (nat_is_trans _ (suc_is_nat _ Q1)) as Q6.
      apply (Q6 _ _ (Q2 Q1 Q5) (suc_i1 k)). }
  apply (induction_principle _ I1 I2 _ P1 P1 P2).
Qed.

Lemma add_less: ∀ m, ∀ p, m ∈ ω → p ∈ ω → m <ₙ (m +ₙ S(p)).
Proof.
  intros m p P1 P2.
  apply (eq_cr (λ x, m <ₙ x) (add_red _ _ P1 P2)).
  pose (λ k, m <ₙ S(m +ₙ k)) as P.
  assert (P 𝟢) as I1.
  { red.
    apply (eq_cr (λ x, m <ₙ S(x)) (add_zero _ P1)).
    apply suc_i1. }
  assert (induction_step P) as I2.
  { intros k Q1 Q2.
    red.
    apply (eq_cr (λ x, m <ₙ S(x)) (add_red _ _ P1 Q1)).
    apply (nat_is_trans (S(S(m +ₙ k))) 
      (suc_is_nat _ (suc_is_nat _ (add_is_nat _ _ P1 Q1)))
      _ _ Q2 (suc_i1 _)). }
  apply (induction_principle _ I1 I2 _ P2).
Qed.

Lemma add_less_equal: ∀ m, ∀ p, m ∈ ω → p ∈ ω → m ≤ₙ (m +ₙ p).
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

Lemma less_less_less: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω → m <ₙ n → n <ₙ p
  → m <ₙ p.
Proof.
  intros m n p P1 P2 P3 P4 P5.
  apply (nat_is_trans _ P3 _ _ P4 P5).
Qed.

Lemma le_less_less: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω → m ≤ₙ n → n <ₙ p
  → m <ₙ p.
Proof.
  intros m n p P1 P2 P3 [P4 | P4] P5.
  + apply (less_less_less _ _ _ P1 P2 P3 P4 P5).
  + apply (eq_cr (λ x, x <ₙ p) P4).
    apply P5.
Qed.

Lemma less_le_less: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω → m <ₙ n → n ≤ₙ p
  → m <ₙ p.
Proof.
  intros m n p P1 P2 P3 P4 [P5 | P5].
  + apply (less_less_less _ _ _ P1 P2 P3 P4 P5).
  + apply (eq_cl (λ x, m <ₙ x) P5).
    apply P4.
Qed.

Lemma le_le_le: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω → m ≤ₙ n → n ≤ₙ p → m ≤ₙ p.
Proof.
  intros m n p P1 P2 P3 [P4 | P4] [P5 | P5].
  + left.
    apply (less_less_less _ _ _ P1 P2 P3 P4 P5).
  + left.
    apply (eq_cl (λ x, m <ₙ x) P5).
    apply P4.
  + left.
    apply (eq_cr (λ x, x <ₙ p) P4).
    apply P5.
  + right.
    apply (eq_t P4 P5).
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
  { destruct (LEM (m = ∅)) as [P4 | P4].
    + right. left.
      apply P4.
    + left.
      apply (empty_in_nat _ P1 P4). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2.
    destruct Q2 as [Q2 | Q2].
    + destruct (suc_eq_or_less _ _ Q1 P1 Q2) as [Q3 | Q3].
      - left.
        apply Q3.
      - right. left.
        apply (eq_s Q3).
    + destruct Q2 as [Q2 | Q2].
      - right. right.
        exists 𝟢.
        split.
        * apply empty_is_nat.
        * apply (eq_cr (λ x, x = S(k)) (add_red _ _ P1 empty_is_nat)).
          apply (eq_cr (λ x, S(x) = S(k)) (add_zero _ P1)).
          apply eq_w.
          apply Q2.
      - destruct Q2 as [p [Q3 Q4]].
        right. right.
        exists (S(p)).
        split.
        * apply (suc_is_nat _ Q3).
        * apply (eq_cr (λ x, x = S(k)) (add_red _ _ P1 (suc_is_nat _ Q3))).
          apply (eq_cr (λ x, S(x) = S(k)) Q4).
          apply eq_r. }
  destruct (induction_principle _ I1 I2 _ P2) as [P4 | P4].
  + apply bot_e.
    apply (nat_not_in_self _ P1).
    apply (nat_is_trans _ P1 _ _ P3 P4).
  + destruct P4 as [P4 | P4].
    - apply bot_e.
      apply (nat_not_in_self _ P2).
      apply (eq_cl (λ x, x <ₙ n) P4 P3).
    - apply P4.
Qed.

(*Lemma order_inequation: ∀ m, ∀ n, ∀ p, ∀ q, m ∈ ω → n ∈ ω → p ∈ ω → q ∈ ω →*)
  (*m <ₙ n → p <ₙ q → ((m ×ₙ q) +ₙ (n ×ₙ p)) <ₙ ((m ×ₙ p) +ₙ (n ×ₙ q)).*)
(*Proof.*)
  (*intros m n p q P1 P2 P3 P4 P5 P6.*)
  (*destruct (less_ex _ _ P1 P2 P5) as [s1 [P7 P8]].*)
  (*destruct (less_ex _ _ P3 P4 P6) as [s2 [P9 P10]].*)
  (*rewrite <- P8.*)
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

Lemma less_add_eq: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω → m <ₙ n
  → (m +ₙ p) <ₙ (n +ₙ p).
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
    apply (suc_less _ _ (add_is_nat _ _ P1 Q1) (add_is_nat _ _ P2 Q1)).
    apply Q2. }
  apply (induction_principle _ I1 I2 _ P3).
Qed.

(*Lemma less_add_cancellation: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω*)
  (*→ (m +ₙ p) <ₙ (n +ₙ p) → m <ₙ n.*)
(*Proof.*)
  (*intros m n p P1 P2 P3 P4.*)
  (*destruct (less_ex _ _ (add_is_nat _ _ P1 P3) (add_is_nat _ _ P2 P3) P4) *)
    (*as [r [P5 P6]].*)
  (*apply (ex_less _ _ r P1 P2 P5).*)
  (*apply (add_cancellation _ _ _ *)
    (*(add_is_nat _ _ P1 (suc_is_nat _ P5)) P2 P3).*)
  (*rewrite (add_cyc _ _ _ P1 P3 (suc_is_nat _ P5)) in P6.*)
(*Qed.*)

(*Lemma less_add_less: forall m n p q, m ∈ ω -> n ∈ ω -> p ∈ ω -> q ∈ ω ->*)
  (*m <ₙ n -> p <ₙ q -> m +ₙ p <ₙ (n +ₙ q).*)
(*Proof.*)
  (*intros m n p q P1 P2 P3 P4 P5 P6.*)
  (*pose (less_add_eq _ _ _ P1 P2 P3 P5) as P7.*)
  (*pose (less_add_eq _ _ _ P3 P4 P2 P6) as P8.*)
  (*rewrite (add_commutative _ _ P3 P2) in P8.*)
  (*rewrite (add_commutative _ _ P4 P2) in P8.*)
  (*apply (less_less_less _ (n +ₙ p) _).*)
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

Theorem nat_trichotomy: ∀ m, ∀ n, m ∈ ω → n ∈ ω →
  ( (m <ₙ n) ∧ (m ≠ n) ∧ ~(n <ₙ m)) ∨
  (~(m <ₙ n) ∧ (m = n) ∧ ~(n <ₙ m)) ∨
  (~(m <ₙ n) ∧ (m ≠ n) ∧  (n <ₙ m)).
Proof.
  intros m n P1 P2.
  pose (λ k, k ∈ ω → k ∈ n ∨ k = n ∨ n ∈ k) as P.
  assert (P (𝟢)) as I1.
  { intros Q1.
    destruct (LEM (n = 𝟢)) as [Q2 | Q2].
    + right. left.
      symmetry.
      apply Q2.
    + left.
      apply (empty_in_nat _ P2 Q2). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 Q3.
    pose (in_nat_nat _ _ Q3 (suc_i1 k)) as Q4.
    destruct (Q2 Q4) as [Q5|[Q5|Q5]].
    + destruct (suc_e _ _ (suc_less _ _ Q4 P2 Q5)) as [Q6|Q6].
      - right. left.
        apply Q6.
      - left.
        apply Q6.
    + right. right.
      apply (eq_cl (λ x, x ∈ S(k)) Q5).
      apply suc_i1.
    + right. right.
      apply (nat_is_trans _ Q3 _ _ Q5 (suc_i1 k)). }
  destruct (induction_principle _ I1 I2 _ P1 P1) as [P5|[P5|P5]].
  + left.
    split.
    { apply P5. }
    split.
    { intros P6.
      apply bot_e.
      apply (nat_not_in_self _ P2).
      apply (eq_cl (λ x, x ∈ n) P6 P5). }
    { intros P6.
      apply bot_e.
      apply (nat_not_in_self _ P2).
      apply (nat_is_trans _ P2 _ _ P6 P5). }
  + right. left.
    split. 
    { apply (eq_cr (λ x, ~ x <ₙ n) P5).
      apply (nat_not_in_self _ P2). }
    split.
    { apply P5. }
    { apply (eq_cr (λ x, ~ n <ₙ x) P5).
      apply (nat_not_in_self _ P2). }
  + right. right.
    split.
    { intros P6.
      apply bot_e.
      apply (nat_not_in_self _ P2).
      apply (nat_is_trans _ P2 _ _ P5 P6). }
    split.
    { intros P6.
      apply bot_e.
      apply (nat_not_in_self _ P2).
      apply (eq_cl (λ x, n ∈ x) P6).
      apply P5. }
    { apply P5. }
Qed.

Theorem nat_trichotomy_weak: ∀ m, ∀ n, m ∈ ω → n ∈ ω →
  (m <ₙ n) ∨ (m = n) ∨ (n <ₙ m).
Proof. 
  intros m n P1 P2.
  destruct (nat_trichotomy _ _ P1 P2) as [[P3 _]|[[_ [P3 _]]|[_ [_ P3]]]]. 
  + left. 
    apply P3.
  + right. left.
    apply P3.
  + right. right.
    apply P3.
Qed.

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
