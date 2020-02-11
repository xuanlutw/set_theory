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
Require Import int.int.
Require Import int.order.
Require Import rat.rat.

(* Real Number *)
Definition dedekind_cut (x: set) := 
  (x ⊆ ℚ) /\ (x <> ℚ) /\ (x <> ∅) /\ (forall p q, p ∈ x -> q ∈ ℚ -> q <q p -> q ∈ x) /\
  (~ exists a, (a ∈ x /\ forall b, b ∈ x -> b <q a)).

Definition real_number := (subset_ctor dedekind_cut (𝒫(ℚ))).

Notation ℝ := real_number.

Lemma real_elim: forall A, A ∈ ℝ -> dedekind_cut A.
Proof.
  intros A P1.
  destruct (subset_elim _ _ _ P1) as [_ P2].
  apply P2.
Qed.

Lemma real_exist_out_elmn: forall A, A ∈ ℝ -> exists x, x ∈ ℚ /\ x ∉  A /\
  forall y, y ∈ A -> y <q x.
Proof.
  intros A P1.
  destruct (real_elim _ P1) as [P2 [P3 [_ [P4 _]]]].
  destruct (not_equal_exist _ _ P3) as [x [[P5 P6]|[P5 P6]]].
  + pose (P2 _ P5) as P7.
    contradiction.
  + exists x.
    repeat split.
    - apply P5.
    - apply P6.
    - intros y P7.
      destruct (rat_trichotomy _ _ P5 (P2 _ P7)) as [P8|[P8|P8]].
      * destruct P8 as [P8 _].
        pose (P4 _ _ P7 P5 P8).
        contradiction.
      * destruct P8 as [_ [P8 _]].
        rewrite P8 in P6.
        contradiction.
      * destruct P8 as [_ [_ P8]].
        apply P8.
Qed.

Lemma real_exist_in_elmn: forall A, A ∈ ℝ -> exists x, x ∈ ℚ /\ x ∈ A /\
  forall y, y ∈ ℚ -> y <q x -> y ∈ A.
Proof.
  intros A P1.
  destruct (real_elim _ P1) as [P2 [_ [P3 [P4 _]]]].
  destruct (not_equal_exist _ _ P3) as [x [[P5 P6]|[P5 P6]]].
  + exists x. 
    repeat split.
    - apply (P2 _ P5).
    - apply P5.
    - intros y P7 P8.
      apply (P4 _ _ P5 P7 P8).
  + pose (not_in_empty x) as P7.
    contradiction.
Qed.

Lemma in_real_rat: forall x m, m ∈ ℝ -> x ∈ m -> x ∈ ℚ.
Proof.
  intros x m P1 P2.
  destruct (real_elim _ P1) as [P3 _].
  apply (P3 _ P2).
Qed.

Lemma real_intro: forall A, dedekind_cut A -> A ∈ ℝ.
Proof.
  intros A P1.
  apply subset_intro.
  + apply subset_in_power.
    destruct P1 as [P1 _].
    apply P1.
  + apply P1.
Qed.

Definition rat_to_real (x: set) := (subset_ctor (fun k => k <q x) ℚ).

Notation "r.0" := (rat_to_real q.0).

Lemma rat_to_real_is_real: forall x, x ∈ ℚ -> (rat_to_real x) ∈ ℝ.
Proof.
  intros x P1.
  apply real_intro.
  repeat split.
  + apply subset_elim_2.
  + intros P2.
    absurd (x ∈ ℚ).
    - rewrite <- P2.
      intros P3.
      destruct (subset_elim _ _ _ P3) as [_ P4].
      apply (rat_not_less_self _ P1 P4).
    - apply P1.
  + apply exist_elmn_not_empty.
    exists (x -q q.1).
    apply subset_intro.
    - apply (rat_add_is_rat _ _ P1 (rat_add_inverse_is_rat _ one_is_rat)).
    - apply (rat_less_minus_positive_2 _ _ P1 one_is_rat rat_zero_less_one). 
  + intros p q P2 P3 P4.
    apply subset_intro.
    - apply P3.
    - destruct (subset_elim _ _ _ P2) as [P5 P6].
      apply (rat_less_trans _ p _ P3 P5 P1 P4 P6).
  + intros [a [P2 P3]].
    destruct (subset_elim _ _ _ P2) as [P4 _].
    apply (rat_not_less_self _ P4 (P3 _ P2)).
Qed.

Lemma zero_is_rat: r.0 ∈ ℝ.
Proof.
  apply (rat_to_real_is_real _ zero_is_rat).
Qed.
(*----------------------------------------------------------------------------*)

(* Real Number Additional *)
Definition real_add (A:set) (B:set) := 
  (subset_ctor (fun k => exists x y, x ∈ A /\ y ∈ B /\ x +q y = k) ℚ).

Notation "A +r B" := (real_add A B) (at level 60, no associativity).

Lemma real_add_is_real: forall A B, A ∈ ℝ -> B ∈ ℝ -> (A +r B) ∈ ℝ.
Proof.
  intros A B P1 P2.
  destruct (real_elim _ P1) as [Q1 [Q2 [Q3 [Q4 Q5]]]].
  destruct (real_elim _ P2) as [R1 [R2 [R3 [R4 R5]]]].
  apply real_intro.
  repeat split.
  + apply subset_elim_2. 
  + destruct(real_exist_out_elmn _ P1) as [a [Q6 [Q7 Q8]]]. 
    destruct(real_exist_out_elmn _ P2) as [b [R6 [R7 R8]]]. 
    apply (exist_not_equal_2 _ _ (a +q b)). 
    - intros P3.
      destruct (subset_elim _ _ _ P3) as [_ [x [y [P4 [P5 P6]]]]].
      pose (Q8 _ P4) as Q9.
      pose (R8 _ P5) as R9.
      pose (rat_less_add _ _ _ _ (Q1 _ P4) Q6 (R1 _ P5) R6 Q9 R9) as P10.
      rewrite P6 in P10.
      apply (rat_not_less_self _ (rat_add_is_rat _ _ Q6 R6) P10).
    - apply (rat_add_is_rat _ _ Q6 R6).
  + intros P3. 
    destruct (not_empty_exist_elmn _ Q3) as [x Q6].
    destruct (not_empty_exist_elmn _ R3) as [y R6].
    assert (x +q y ∈ A +r B) as P4.
    { apply subset_intro.
      + apply (rat_add_is_rat _ _ (Q1 _ Q6) (R1 _ R6)).
      + exists x.
        exists y.
        repeat split.
        - apply Q6.
        - apply R6. }
    rewrite P3 in P4.
    apply (not_in_empty _ P4).
  + intros p q P3 P4 P5.
    destruct (subset_elim _ _ _ P3) as [P6 [x [y [P7 [P8 P9]]]]].
    apply (subset_intro).
    - apply P4.
    - exists x.
      pose (rat_less_positive _ _ P4 P6 P5) as P10.
      exists (y -q (p -q q)).
      repeat split.
      * apply P7.
      * apply (R4 _ _ P8).
        ++apply (rat_add_is_rat _ _ (R1 _ P8)).
          apply rat_add_inverse_is_rat.
          apply (rat_add_is_rat _ _ P6 (rat_add_inverse_is_rat _ P4)).
        ++apply (rat_less_minus_positive_2 _ _ (R1 _ P8)
          (rat_add_is_rat _ _ P6 (rat_add_inverse_is_rat _ P4)) P10).
      * rewrite (rat_add_associative x y (-q (p -q q))).
        rewrite P9.
        rewrite (rat_inverse_add_distributive p (-q q)).
        rewrite (rat_add_associative p (-q p) (-q (-q q))).
        rewrite (rat_add_inverse_elim p).
        rewrite (rat_double_inverse_elim q).
        rewrite (rat_add_commutative q.0 q).
        rewrite (rat_add_zero q).
        all: is_rat.
        apply (Q1 _ P7).
        apply (R1 _ P8).
  + intros P3. 
    destruct P3 as [s [P3 P4]].
    destruct (subset_elim _ _ _ P3) as [P6 [x [y [P7 [P8 P9]]]]].
    absurd (exists a : set, a ∈ A /\ (forall b : set, b ∈ A -> b <q a)).
    - apply Q5.
    - exists x.
      split.
      * apply P7.
      * intros b P10.
        apply (rat_less_add_cancellation _ _ _ (Q1 _ P10) (Q1 _ P7) (R1 _ P8)).
        rewrite P9.
        apply P4.
        apply subset_intro.
        ++apply (rat_add_is_rat _ _ (Q1 _ P10) (R1 _ P8)).
        ++exists b. exists y.
          repeat split.
          --apply P10.
          --apply P8.
Qed.

Lemma in_real_add_elim: forall x A B, x ∈ A +r B -> 
  exists a b, a ∈ A /\ b ∈ B /\ a +q b = x.
Proof.
  intros x A B P1.
  destruct (subset_elim _ _ _ P1) as [P2 [a [b P3]]].
  exists a. exists b.
  apply P3.
Qed.

Lemma in_real_add_rat: forall x A B, x ∈ A +r B -> x ∈ ℚ.
Proof.
  intros x A B P1.
  destruct (subset_elim _ _ _ P1) as [P2 [a [b P3]]].
  apply P2.
Qed.

Lemma in_real_add_intro_1: forall x y A B, A ∈ ℝ -> B ∈ ℝ -> x ∈ A -> y ∈ B ->
  x +q y ∈ A +r B.
Proof.
  intros x y A B P1 P2 P3 P4.
  apply subset_intro.
  + apply (rat_add_is_rat _ _ (in_real_rat _ _ P1 P3) (in_real_rat _ _ P2 P4)).
  + exists x.
    exists y.
    repeat split.
    - apply P3.
    - apply P4.
Qed.

Lemma real_add_commutative: forall m n, m ∈ ℝ -> n ∈ ℝ -> m +r n = n +r m.
Proof.
  intros m n P1 P2.
  apply ax_exten.
  intros s.
  split.
  + intros P3.
    apply subset_intro.
    - apply (in_real_add_rat _ _ _ P3). 
    - destruct (in_real_add_elim _ _ _ P3) as [x [y [P4 [P5 P6]]]].
      exists y. exists x.
      repeat split.
      * apply P5.
      * apply P4.
      * rewrite (rat_add_commutative _ _ 
          (in_real_rat _ _ P2 P5) (in_real_rat _ _ P1 P4)).
        apply P6.
  + intros P3.
    apply subset_intro.
    - apply (in_real_add_rat _ _ _ P3). 
    - destruct (in_real_add_elim _ _ _ P3) as [x [y [P4 [P5 P6]]]].
      exists y. exists x.
      repeat split.
      * apply P5.
      * apply P4.
      * rewrite (rat_add_commutative _ _ 
          (in_real_rat _ _ P1 P5) (in_real_rat _ _ P2 P4)).
        apply P6.
Qed. 

Lemma real_add_associative: forall m n l, m ∈ ℝ -> n ∈ ℝ -> l ∈ ℝ ->
  m +r (n +r l) = (m +r n) +r l.
Proof.
  intros m n l P1 P2 P3.
  apply subset_asym.
  split.
  + intros s P4.
    apply subset_intro.
    - apply (in_real_add_rat _ _ _ P4). 
    - destruct (in_real_add_elim _ _ _ P4) as [a [p [P5 [P6 P7]]]].
      destruct (in_real_add_elim _ _ _ P6) as [b [c [P8 [P9 P10]]]].
      exists (a +q b).
      exists c.
      repeat split.
      * apply (in_real_add_intro_1 _ _ _ _ P1 P2 P5 P8).
      * apply P9.
      * rewrite <- (rat_add_associative _ _ _ (in_real_rat _ _ P1 P5)
          (in_real_rat _ _ P2 P8) (in_real_rat _ _ P3 P9)).
        rewrite P10.
        apply P7.
  + intros s P4.
    apply subset_intro.
    - apply (in_real_add_rat _ _ _ P4). 
    - destruct (in_real_add_elim _ _ _ P4) as [p [c [P5 [P6 P7]]]].
      destruct (in_real_add_elim _ _ _ P5) as [a [b [P8 [P9 P10]]]].
      exists a.
      exists (b +q c).
      repeat split.
      * apply P8.
      * apply (in_real_add_intro_1 _ _ _ _ P2 P3 P9 P6).
      * rewrite (rat_add_associative _ _ _ (in_real_rat _ _ P1 P8)
          (in_real_rat _ _ P2 P9) (in_real_rat _ _ P3 P6)).
        rewrite P10.
        apply P7.
Qed. 

(*Lemma real_add_zero: forall m, m ∈ ℝ -> m +r r.0 = m.*)
(*Proof.*)
  (*intros m P1.*)
  (*apply subset_asym.*)
  (*split.*)
  (*+ intros s P2.*)
    (*destruct (in_real_add_elim _ _ _ P2) as [x [y [P3 [P4 P5]]]].*)
(*----------------------------------------------------------------------------*)
