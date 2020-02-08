Require Import axiom.axiom.
Require Import axiom.logic.
Require Import operation.basic.
Require Import relation.relation.
Require Import relation.function.
Require Import relation.util_function.
Require Import relation.equiv.
Require Import nat.inductive.
Require Import nat.nat.
Require Import nat.recursion.
Require Import nat.nat_arith.
Require Import nat.order.
Require Import int.int.

(* Order *)
Definition int_less_rel :=
  subset_ctor (fun x => exists m n p q, m ∈ ω /\ n ∈ ω /\ p ∈ ω /\ q ∈ ω /\
    x = ⟨int m n , int p q⟩ /\ ((m +ₙ q) <ₙ (n +ₙ p))) (cp ℤ ℤ).

Notation "m <z n" := (⟨m, n⟩ ∈ int_less_rel) (at level 65, no associativity).

Lemma int_less_elim_1: forall x y, x ∈ ℤ -> y ∈ ℤ -> x <z y ->
  exists m n p q, m ∈ ω /\ n ∈ ω /\ p ∈ ω /\ q ∈ ω /\
    x = int m n /\ y = int p q /\ (m +ₙ q) <ₙ (n +ₙ p).
Proof.
  intros x y P1 P2 P3.
  destruct (subset_elim _ _ _ P3) as [P4 [m [n [p [q [Q1 [Q2 [Q3 [Q4 [P5 P6]]]]]]]]]].
  exists m. exists n. exists p. exists q.
  repeat split.
  all: is_nat.
  + apply (opair_equal_elim_fst _ _ _ _ P5).
  + apply (opair_equal_elim_snd _ _ _ _ P5).
Qed.

Lemma int_less_elim_2: forall m n p q, m ∈ ω -> n ∈ ω -> p ∈ ω -> q ∈ ω -> 
  int m n <z int p q -> (m +ₙ q) <ₙ (n +ₙ p).
Proof.
  intros m n p q P1 P2 P3 P4 P5.
  destruct (int_less_elim_1 _ _ (int_ctor_is_int _ _ P1 P2)
    (int_ctor_is_int _ _ P3 P4) P5) 
    as [m2 [n2 [p2 [q2 [R1 [R2 [R3 [R4 [P6 [P7 P8]]]]]]]]]].
  pose (int_equal_elim _ _ _ _ P1 P2 P6) as Q1.
  pose (int_equal_elim _ _ _ _ P3 P4 P7) as Q2.
  symmetry in Q2.
  pose (add_equation _ _ _ _ Q1 Q2) as Q3.
  rewrite (add_associative (m +ₙ n2) q p2) in Q3.
  rewrite (add_cyc m n2 q) in Q3.
  rewrite <- (add_associative (m +ₙ q) n2 p2) in Q3.
  rewrite (add_associative (n +ₙ m2) p q2) in Q3.
  rewrite (add_cyc n m2 p) in Q3.
  rewrite <- (add_associative (n +ₙ p) m2 q2) in Q3.
  rewrite (add_commutative (m +ₙ q) (n2 +ₙ p2)) in Q3.
  rewrite (add_commutative (n +ₙ p) (m2 +ₙ q2)) in Q3.
  symmetry in Q3.
  apply (equal_less_less (m2 +ₙ q2) (n2 +ₙ p2) _ _).
  all: is_nat_z4.
Qed.

Lemma int_less_intro: forall m n p q, m ∈ ω -> n ∈ ω -> p ∈ ω -> q ∈ ω -> 
  (m +ₙ q) <ₙ (n +ₙ p) -> int m n <z int p q .
Proof.
  intros m n p q P1 P2 P3 P4 P5.
  apply (subset_intro).
  + is_nat_z3.
  + exists m. exists n. exists p. exists q.
    repeat split.
    all: is_nat.
Qed.

Lemma int_less_trans: forall m n l, m ∈ ℤ -> n ∈ ℤ -> l ∈ ℤ ->
 m <z n -> n <z l -> m <z l.
Proof.
  intros m n l P1 P2 P3 P4 P5.
  destruct (int_less_elim_1 _ _ P1 P2 P4) as 
    [q1 [q2 [r1 [r2 [Q1 [Q2 [R1 [R2 [Q3 [R3 P6]]]]]]]]]].
  destruct (int_less_elim_1 _ _ P2 P3 P5) as 
    [s1 [s2 [t1 [t2 [S1 [S2 [T1 [T2 [S3 [T3 P7]]]]]]]]]].
  rewrite R3 in S3.
  pose (int_equal_elim _ _ _ _ R1 R2 S3) as P8.
  rewrite Q3.
  rewrite T3.
  pose (less_add_eq _ _ _ 
    (add_is_nat _ _ Q1 R2) (add_is_nat _ _ Q2 R1) 
    (add_is_nat _ _ S2 T2) P6) as P9. 
  rewrite (add_associative (q2 +ₙ r1) s2 t2) in P9.
  rewrite <- (add_associative q2 r1 s2) in P9.
  rewrite (add_commutative q2 (r1 +ₙ s2)) in P9.
  rewrite <- (add_associative (r1 +ₙ s2) q2 t2) in P9.
  rewrite (add_commutative s2 t2) in P9.
  rewrite (add_associative (q1 +ₙ r2) t2 s2) in P9.
  rewrite (add_cyc q1 r2 t2) in P9.
  rewrite <- (add_associative (q1 +ₙ t2) r2 s2) in P9.
  
  pose (less_add_eq _ _ _ 
    (add_is_nat _ _ S1 T2) (add_is_nat _ _ S2 T1) 
    (add_is_nat _ _ R2 Q2) P7) as P10. 
  rewrite (add_associative (s1 +ₙ t2) r2 q2) in P10.
  rewrite (add_cyc s1 t2 r2) in P10.
  rewrite <- (add_associative (s1 +ₙ r2) t2 q2) in P10.
  rewrite (add_commutative s1 r2) in P10.
  rewrite (add_commutative t2 q2) in P10.
  rewrite (add_commutative r2 q2) in P10.
  rewrite (add_associative (s2 +ₙ t1) q2 r2) in P10.
  rewrite <- (add_associative s2 t1 q2) in P10.
  rewrite (add_commutative s2 (t1 +ₙ q2)) in P10.
  rewrite <- (add_associative (t1 +ₙ q2) s2 r2) in P10.
  rewrite (add_commutative t1 q2) in P10.
  rewrite (add_commutative s2 r2) in P10.
  rewrite <- P8 in P10.
  apply int_less_intro.
  all: is_nat.
  apply (less_add_cancellation _ _ (r2 +ₙ s2)).
  all: is_nat.
  apply (less_less_less _ ((r1 +ₙ s2) +ₙ (q2 +ₙ t2)) _). 
  all: is_nat.
Qed.

Lemma int_trichotomy: forall m n, m ∈ ℤ -> n ∈ ℤ ->
  ((m <z n) /\ ~(m = n) /\ ~(n <z m)) \/
  (~(m <z n) /\ (m = n) /\ ~(n <z m)) \/
  (~(m <z n) /\ ~(m = n) /\ (n <z m)).
Proof.
  intros m n P1 P2.
  destruct (int_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (int_elim _ P2) as [rm [rn [R1 [R2 R3]]]]. 
  rewrite Q3.
  rewrite R3.
  destruct (nat_trichotomy (qm +ₙ rn) (qn +ₙ rm)
    (add_is_nat _ _ Q1 R2) (add_is_nat _ _ Q2 R1)) 
      as [[P3 [P4 P5]] | [[P3 [P4 P5]] | [P3 [P4 P5]]]].
  + left.
    repeat split.
    - apply int_less_intro.
      all: is_nat.
    - intros P6.
      pose (int_equal_elim _ _ _ _ Q1 Q2 P6) as P7.
      contradiction.
    - intros P6.
      pose (int_less_elim_2 _ _ _ _ R1 R2 Q1 Q2 P6) as P7.
      rewrite (add_commutative _ _ Q2 R1) in P5.
      rewrite (add_commutative _ _ Q1 R2) in P5.
      contradiction.
  + right. left.
    repeat split.
    - intros P6.
      pose (int_less_elim_2 _ _ _ _ Q1 Q2 R1 R2 P6) as P7.
      contradiction.
    - apply (int_equal_intro _ _ _ _ Q1 Q2 R1 R2 P4). 
    - intros P6.
      pose (int_less_elim_2 _ _ _ _ R1 R2 Q1 Q2 P6) as P7.
      rewrite (add_commutative _ _ Q2 R1) in P5.
      rewrite (add_commutative _ _ Q1 R2) in P5.
      contradiction.
  + right. right.
    repeat split.
    - intros P6.
      pose (int_less_elim_2 _ _ _ _ Q1 Q2 R1 R2 P6) as P7.
      contradiction.
    - intros P6.
      pose (int_equal_elim _ _ _ _ Q1 Q2 P6) as P7.
      contradiction.
    - rewrite (add_commutative _ _ Q2 R1) in P5.
      rewrite (add_commutative _ _ Q1 R2) in P5.
      apply int_less_intro.
      all: is_nat.
Qed.

Lemma int_less_add_equal: forall m n l, m ∈ ℤ -> n ∈ ℤ -> l ∈ ℤ ->
  m <z n -> (m +z l) <z (n +z l).
Proof.
  intros m n l P1 P2 P3 P4.
  destruct (int_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (int_elim _ P2) as [rm [rn [R1 [R2 R3]]]]. 
  destruct (int_elim _ P3) as [sm [sn [S1 [S2 S3]]]]. 
  rewrite Q3 in P4.
  rewrite R3 in P4.
  pose (int_less_elim_2 _ _ _ _ Q1 Q2 R1 R2 P4) as P5.
  rewrite Q3.
  rewrite R3.
  rewrite S3.
  rewrite (int_add_elim qm qn sm sn).
  rewrite (int_add_elim rm rn sm sn).
  apply int_less_intro.
  all: is_nat.
  rewrite (add_associative (qm +ₙ sm) rn sn).
  rewrite (add_cyc qm sm rn).
  rewrite <- (add_associative (qm +ₙ rn) sm sn).
  rewrite (add_associative (qn +ₙ sn) rm sm).
  rewrite (add_cyc qn sn rm).
  rewrite <- (add_associative (qn +ₙ rm) sn sm).
  rewrite (add_commutative sn sm).
  apply (less_add_eq).
  all: is_nat.
Qed.

Lemma int_less_multi_equal: forall m n l, m ∈ ℤ -> n ∈ ℤ -> l ∈ ℤ -> 
  z.0 <z l -> m <z n -> (m ×z l) <z (n ×z l).
Proof.
  intros m n l P1 P2 P3 P4 P5.
  destruct (int_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (int_elim _ P2) as [rm [rn [R1 [R2 R3]]]]. 
  destruct (int_elim _ P3) as [sm [sn [S1 [S2 S3]]]]. 
  rewrite S3 in P4.
  pose (int_less_elim_2 _ _ _ _ empty_is_nat empty_is_nat S1 S2 P4) as P6.
  rewrite Q3 in P5.
  rewrite R3 in P5.
  pose (int_less_elim_2 _ _ _ _ Q1 Q2 R1 R2 P5) as P7.
  rewrite Q3.
  rewrite R3.
  rewrite S3.
  rewrite (int_multi_elim qm qn sm sn).
  rewrite (int_multi_elim rm rn sm sn).
  apply int_less_intro.
  all: is_nat.
  rewrite (add_zero_l sn) in P6.
  rewrite (add_zero_l sm) in P6.
  rewrite <- (add_associative (qm ×ₙ sm) (qn ×ₙ sn) ((rm ×ₙ sn) +ₙ (rn ×ₙ sm))).
  rewrite (add_associative (qn ×ₙ sn) (rm ×ₙ sn) (rn ×ₙ sm)).
  rewrite (add_commutative (qn ×ₙ sn +ₙ rm ×ₙ sn) (rn ×ₙ sm)).
  rewrite (add_associative (qm ×ₙ sm) (rn ×ₙ sm) (qn ×ₙ sn +ₙ rm ×ₙ sn)).
  rewrite <- (distributive_r qm rn sm).
  rewrite <- (distributive_r qn rm sn).
  rewrite <- (add_associative (qm ×ₙ sn) (qn ×ₙ sm) ((rm ×ₙ sm) +ₙ (rn ×ₙ sn))).
  rewrite (add_associative (qn ×ₙ sm) (rm ×ₙ sm) (rn ×ₙ sn)).
  rewrite (add_commutative (qn ×ₙ sm +ₙ rm ×ₙ sm) (rn ×ₙ sn)).
  rewrite (add_associative (qm ×ₙ sn) (rn ×ₙ sn) (qn ×ₙ sm +ₙ rm ×ₙ sm)).
  rewrite <- (distributive_r qm rn sn).
  rewrite <- (distributive_r qn rm sm).
  apply order_inequation.
  all: is_nat.
Qed.

Lemma int_add_cancellation: forall m n l, m ∈ ℤ -> n ∈ ℤ -> l ∈ ℤ ->
  m +z l = n +z l -> m = n.
Proof.
  intros m n l P1 P2 P3 P4.
  destruct (int_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (int_elim _ P2) as [rm [rn [R1 [R2 R3]]]]. 
  destruct (int_elim _ P3) as [sm [sn [S1 [S2 S3]]]]. 
  rewrite Q3 in P4.
  rewrite R3 in P4.
  rewrite S3 in P4.
  rewrite (int_add_elim qm qn sm sn) in P4.
  rewrite (int_add_elim rm rn sm sn) in P4.
  pose (int_equal_elim (qm +ₙ sm) (qn +ₙ sn) (rm +ₙ sm) (rn +ₙ sn)
    (add_is_nat _ _ Q1 S1) (add_is_nat _ _ Q2 S2) P4) as P5.
  rewrite (add_associative (qm +ₙ sm) rn sn) in P5.
  rewrite (add_cyc qm sm rn)in P5.
  rewrite <- (add_associative (qm +ₙ rn) sm sn) in P5.
  rewrite (add_associative (qn +ₙ sn) rm sm) in P5.
  rewrite (add_cyc qn sn rm)in P5.
  rewrite <- (add_associative (qn +ₙ rm) sn sm) in P5.
  rewrite (add_commutative sn sm) in P5.
  rewrite Q3.
  rewrite R3.
  apply (int_equal_intro).
  all: is_nat.
  apply (add_cancellation _ _ (sm +ₙ sn)).
  all: is_nat.
Qed.

Lemma int_multi_cancellation: forall m n l, m ∈ ℤ -> n ∈ ℤ -> l ∈ ℤ' ->
  m ×z l = n ×z l -> m = n.
Proof.
  intros m n l P1 P2 P3 P4.
  destruct (int_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (int_elim _ P2) as [rm [rn [R1 [R2 R3]]]]. 
  destruct (int_elim _ (in_subz _ P3)) as [sm [sn [S1 [S2 S3]]]]. 
  rewrite Q3 in P4.
  rewrite R3 in P4.
  rewrite S3 in P4.
  rewrite (int_multi_elim qm qn sm sn) in P4.
  rewrite (int_multi_elim rm rn sm sn) in P4.
  assert (((qm ×ₙ sm +ₙ qn ×ₙ sn) +ₙ (rm ×ₙ sn +ₙ rn ×ₙ sm))
    = ((qm ×ₙ sn +ₙ qn ×ₙ sm) +ₙ (rm ×ₙ sm +ₙ rn ×ₙ sn))) as P5.
  { apply (int_equal_elim).
    all: is_nat. }
  rewrite (add_commutative (rm ×ₙ sn) (rn ×ₙ sm)) in P5.
  rewrite (add_associative (qm ×ₙ sm +ₙ qn ×ₙ sn) (rn ×ₙ sm) (rm ×ₙ sn)) in P5.
  rewrite (add_cyc (qm ×ₙ sm) (qn ×ₙ sn) (rn ×ₙ sm)) in P5.
  rewrite <- (add_associative (qm ×ₙ sm +ₙ rn ×ₙ sm) (qn ×ₙ sn) (rm ×ₙ sn)) in P5.
  rewrite <- (distributive_r qm rn sm) in P5.
  rewrite <- (distributive_r qn rm sn) in P5.
  rewrite (add_commutative (rm ×ₙ sm) (rn ×ₙ sn)) in P5.
  rewrite (add_associative (qm ×ₙ sn +ₙ qn ×ₙ sm) (rn ×ₙ sn) (rm ×ₙ sm)) in P5.
  rewrite (add_cyc (qm ×ₙ sn) (qn ×ₙ sm) (rn ×ₙ sn)) in P5.
  rewrite <- (add_associative (qm ×ₙ sn +ₙ rn ×ₙ sn) (qn ×ₙ sm) (rm ×ₙ sm)) in P5.
  rewrite <- (distributive_r qm rn sn) in P5.
  rewrite <- (distributive_r qn rm sm) in P5.
  rewrite Q3.
  rewrite R3.
  apply (int_equal_intro).
  all: is_nat.
  pose (in_subz_not_zero _ P3) as P6.
  rewrite S3 in P6.
  pose (int_not_zero_elim _ _ S1 S2 P6) as P7.
  apply (not_equal_cyc_equal _ _ sm sn).
  all: is_nat.
Qed.
(*----------------------------------------------------------------------------*)
