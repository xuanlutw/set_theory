Require Import axiom.axiom.
Require Import axiom.logic.
Require Import operation.basic.
Require Import relation.relation.
Require Import relation.function.
Require Import relation.util_function.
Require Import nat.inductive.
Require Import nat.nat.
Require Import nat.recursion.

(* Addition *)
Definition σ := subset_ctor 
  (fun x => exists y, x = ⟨y, S(y)⟩) (cp ω ω).

Lemma sigma_is_function: fover σ ω ω.
Proof.
  split. split.
  + intros x P1.
    destruct (subset_elim _ _ _ P1) as [_ [y P2]].
    exists y.
    exists (S(y)).
    apply P2.
  + intros a b1 b2 P1 P2.
    destruct (subset_elim _ _ _ P1) as [_ [y1 P3]].
    destruct (opair_equal_elim _ _ _ _ P3) as [P4 P5].
    rewrite P5.
    rewrite <- P4.
    destruct (subset_elim _ _ _ P2) as [_ [y2 P6]].
    destruct (opair_equal_elim _ _ _ _ P6) as [P7 P8].
    rewrite P8.
    rewrite <- P7.
    reflexivity. 
  + split.
    - apply ax_exten.
      intros x.
      split.
      * intros P1.
        destruct (dom_elim _ _ P1) as [y P2].
        destruct (subset_elim _ _ _ P2) as [P3 _].
        destruct (cp_elim _ _ _ P3) as [nx [ny [P4 [_ P5]]]].
        destruct (opair_equal_elim _ _ _ _ P5) as [P6 _].
        rewrite P6.
        apply P4.
      * intros P2.
        apply dom_intro.
        exists (S(x)).
        apply subset_intro.
        { apply cp_intro.
          + apply P2.
          + apply (suc_is_nat _ P2). }
        { exists x.
          reflexivity. }
    - intros y P1.
      destruct (ran_elim _ _ P1) as [x P2].
      destruct (subset_elim _ _ _ P2) as [P3 _].
      destruct (cp_elim _ _ _ P3) as [nx [ny [_ [P4 P5]]]].
      destruct (opair_equal_elim _ _ _ _ P5) as [_ P6].
      rewrite P6.
      apply P4.
Qed.

Lemma sigma_intro: forall k, k ∈ ω -> S(k) = σ[k].
Proof.
  intros k P1.
  apply fval_intro.
  + destruct sigma_is_function as [P2 _].
    apply P2.
  + apply subset_intro.
    - apply cp_intro.
      * apply P1.
      * apply (suc_is_nat _ P1).
    - exists k.
      reflexivity.
Qed.

Definition add_proto (m: set) :=
  extract_set (recursion_theorem ω m σ).

Lemma add_proto_is_function: forall m, m ∈ ω -> fover (add_proto m) ω ω.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω m σ) P1 sigma_is_function)
    as [P2 _].
  apply P2.
Qed.

Lemma add_proto_elim_1: forall m, m ∈ ω -> (add_proto m)[∅] = m.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω m σ) P1 sigma_is_function) 
    as [_ [P2 _]].
  apply P2.
Qed.

Lemma add_proto_elim_2: forall m n, m ∈ ω -> n ∈ ω -> 
    (add_proto m)[S(n)] = S((add_proto m)[n]).
Proof.
  intros m n P1 P2.
  destruct (extract_set_property (recursion_theorem ω m σ) P1 sigma_is_function) 
    as [[P3 [P4 P5]] [_ P6]].
  assert ((extract_set (recursion_theorem ω m σ))[n] ∈ ω) as P7.
  { apply P5. 
    apply fval_ran.
    + apply P3.
    + rewrite P4.
      apply P2. }
  pose (P6 n) as P8.
  rewrite <- (sigma_intro _ P7) in P8.
  apply P8.
  apply P2.
Qed.
 
Notation "m +ₙ n" := ((add_proto m)[n]) (at level 65, no associativity).

Notation "n.0" := ∅         .
Notation "n.1" := (S(∅))    .
Notation "n.2" := (S(S(∅))) .

Lemma one_is_nat: n.1 ∈ ω.
Proof.
  apply (suc_is_nat _ empty_is_nat).
Qed.

Lemma add_zero: forall m, m ∈ ω -> m +ₙ n.0 = m.
Proof.
  intros m P1.
  apply (add_proto_elim_1 _ P1).
Qed.

Lemma add_red: forall m n, m ∈ ω -> n ∈ ω -> m +ₙ S(n) = S(m +ₙ n).
Proof.
  intros m n P1 P2.
  apply (add_proto_elim_2 _ _ P1 P2).
Qed.

Lemma add_is_nat: forall m n, m ∈ ω -> n ∈ ω -> m +ₙ n ∈ ω.
Proof.
  intros m n P1 P2.
  destruct (add_proto_is_function _ P1) as [P3 [P4 P5]].
  apply P5.
  apply ran_intro.
  exists n.
  apply fval_intro_2.
  + apply P3.
  + rewrite P4.
    apply P2.
Qed.

Theorem one_one_two: n.1 +ₙ n.1 = n.2.
Proof.
  assert (n.1 ∈ ω) as P1.
  { apply suc_is_nat. 
    apply empty_is_nat. }
  rewrite (add_red (n.1) (n.0) P1 empty_is_nat).
  rewrite (add_zero (n.1) P1).
  reflexivity.
Qed.
(*----------------------------------------------------------------------------*)

(* Multiplication *)
Definition multi_proto (m: set) :=
  extract_set (recursion_theorem ω (n.0) (add_proto m)).

Lemma multi_proto_is_function: forall m, m ∈ ω -> fover (multi_proto m) ω ω.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω (n.0) (add_proto m)) 
    (empty_is_nat) (add_proto_is_function _ P1)) as [P2 _].
  apply P2.
Qed.

Lemma multi_proto_elim_1: forall m, m ∈ ω -> (multi_proto m)[n.0] = n.0.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω (n.0) (add_proto m)) 
    (empty_is_nat) (add_proto_is_function _ P1)) as [_ [P2 _]].
  apply P2.
Qed.

Lemma multi_proto_elim_2: forall m n, m ∈ ω -> n ∈ ω -> 
    (multi_proto m)[S(n)] = (add_proto m)[(multi_proto m)[n]].
Proof.
  intros m n P1 P2.
  destruct (extract_set_property (recursion_theorem ω n.0 (add_proto m)) 
    (empty_is_nat) (add_proto_is_function _ P1)) as [_ [_ P3]].
  apply (P3 _ P2).
Qed.
    
Notation "m ×ₙ n" := ((multi_proto m)[n]) (at level 64, no associativity).

Lemma multi_zero: forall m, m ∈ ω -> m ×ₙ n.0 = n.0.
Proof.
  intros m P1.
  apply (multi_proto_elim_1 _ P1).
Qed.

Lemma multi_red: forall m n, m ∈ ω -> n ∈ ω -> m ×ₙ S(n) = m +ₙ (m ×ₙ n).
Proof.
  intros m n P1 P2.
  apply (multi_proto_elim_2 _ _ P1 P2).
Qed.

Lemma multi_is_nat: forall m n, m ∈ ω -> n ∈ ω -> m ×ₙ n ∈ ω.
Proof.
  intros m n P1 P2.
  destruct (multi_proto_is_function _ P1) as [P3 [P4 P5]].
  apply P5.
  apply ran_intro.
  exists n.
  apply fval_intro_2.
  + apply P3.
  + rewrite P4.
    apply P2.
Qed.
(*----------------------------------------------------------------------------*)

(* Exponential *)
Definition exp_proto (m: set) :=
  extract_set (recursion_theorem ω (n.1) (multi_proto m)).

Lemma exp_proto_is_function: forall m, m ∈ ω -> fover (exp_proto m) ω ω.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω n.1 (multi_proto m)) 
    one_is_nat (multi_proto_is_function _ P1)) as [P2 _].
  apply P2.
Qed.

Lemma exp_proto_elim_1: forall m, m ∈ ω -> (exp_proto m)[n.0] = n.1.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω n.1 (multi_proto m)) 
    one_is_nat (multi_proto_is_function _ P1)) as [_ [P2 _]].
  apply P2.
Qed.

Lemma exp_proto_elim_2: forall m n, m ∈ ω -> n ∈ ω -> 
    (exp_proto m)[S(n)] = (multi_proto m)[(exp_proto m)[n]].
Proof.
  intros m n P1 P2.
  destruct (extract_set_property (recursion_theorem ω n.1 (multi_proto m)) 
    (one_is_nat) (multi_proto_is_function _ P1)) as [_ [_ P3]].
  apply (P3 _ P2).
Qed.

Notation "m ^ₙ n" := ((exp_proto m)[n]) (at level 65, no associativity).

Lemma exp_zero: forall m, m ∈ ω -> m ^ₙ n.0 = n.1.
Proof.
  intros m P1.
  apply (exp_proto_elim_1 _ P1).
Qed.

Lemma exp_red: forall m n, m ∈ ω -> n ∈ ω -> m ^ₙ S(n) = m ×ₙ (m ^ₙ n).
Proof.
  intros m n P1 P2.
  apply (exp_proto_elim_2 _ _ P1 P2).
Qed.
(*----------------------------------------------------------------------------*)

(* Arith Law *)
Lemma add_zero_l: forall m, m ∈ ω -> n.0 +ₙ m = m.
Proof.
  intros m P1.
  assert (n.0 +ₙ n.0 = n.0) as P2.
  { apply (add_zero _ empty_is_nat). }
  assert (forall k, k ∈ ω -> n.0 +ₙ k = k -> n.0 +ₙ S(k) = S(k)) as P3.
  { intros k P3 P4.
    rewrite (add_red _ _ empty_is_nat P3).
    f_equal.
    apply P4. }
  apply (induction_principle _ P2 P3 _ P1).
Qed.

Lemma add_red_l: forall m n, m ∈ ω -> n ∈ ω -> S(m) +ₙ n = S(m +ₙ n).
Proof.
  intros m n P1 P2.
  assert (S(m) +ₙ n.0 = S(m +ₙ n.0)) as P3.
  { rewrite (add_zero _ (suc_is_nat _ P1)).
    rewrite (add_zero _ P1).
    reflexivity. }
  assert (forall k, k ∈ ω -> 
    S(m) +ₙ k = S(m +ₙ k) -> S(m) +ₙ S(k) = S(m +ₙ S(k))) as P4.
  { intros k P4 P5.
    rewrite (add_red _ _ (suc_is_nat _ P1) P4).
    rewrite P5.
    f_equal.
    symmetry.
    apply (add_red _ _ P1 P4). }
  apply (induction_principle _ P3 P4 _ P2).
Qed.

Lemma add_commutative: forall m n, m ∈ ω -> n ∈ ω -> m +ₙ n = n +ₙ m.
Proof. 
  intros m n P1 P2.
  assert (m +ₙ n.0 = n.0 +ₙ m) as P3.
  { rewrite (add_zero _ P1).
    rewrite (add_zero_l _ P1).
    reflexivity. }
  assert (forall k, k ∈ ω -> m +ₙ k = k +ₙ m -> m +ₙ S(k) = S(k) +ₙ m) as P4.
  { intros k P4 P5.
    rewrite (add_red _ _ P1 P4).
    rewrite (add_red_l _ _ P4 P1).
    f_equal.
    apply P5. }
  apply (induction_principle _ P3 P4 _ P2).
Qed.

Lemma add_associative: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->
  m +ₙ (n +ₙ p) = (m +ₙ n) +ₙ p.
Proof.
  intros m n p P1 P2 P3.
  assert (m +ₙ (n +ₙ n.0) = (m +ₙ n) +ₙ n.0) as P4.
  { rewrite (add_zero _ P2).
    symmetry.    
    apply add_zero.
    apply (add_is_nat _ _ P1 P2). }
  assert (forall k, k ∈ ω -> m +ₙ (n +ₙ k) = (m +ₙ n) +ₙ k ->
    m +ₙ (n +ₙ S(k)) = (m +ₙ n) +ₙ S(k)) as P5.
  { intros k P5 P6.
    rewrite (add_red _ _ (add_is_nat _ _ P1 P2) P5).
    rewrite <- P6.
    rewrite <- (add_red _ _ P1 (add_is_nat _ _ P2 P5)).
    rewrite <- (add_red _ _ P2 P5).
    reflexivity. }
  apply (induction_principle _ P4 P5 _ P3).
Qed.

Lemma multi_zero_l: forall m, m ∈ ω -> n.0 ×ₙ m = n.0.
Proof.
  intros m P1.
  assert (n.0 ×ₙ n.0 = n.0) as P2.
  { apply (multi_zero _ empty_is_nat). }
  assert (forall k, k ∈ ω -> n.0 ×ₙ k = n.0 -> n.0 ×ₙ S(k) = n.0) as P3.
  { intros k P3 P4.
    rewrite (multi_red _ _ empty_is_nat P3).
    rewrite P4.
    apply (add_zero _ empty_is_nat). }
  apply (induction_principle _ P2 P3 _ P1).
Qed.

Lemma multi_red_l: forall m n, m ∈ ω -> n ∈ ω -> S(m) ×ₙ n = n +ₙ (m ×ₙ n).
Proof.
  intros m n P1 P2.
  assert (S(m) ×ₙ n.0 = n.0 +ₙ (m ×ₙ n.0)) as P3.
  { rewrite (multi_zero _ (suc_is_nat _ P1)).
    rewrite (multi_zero _ P1).
    rewrite (add_zero _ empty_is_nat).
    reflexivity. }
  assert (forall k, k ∈ ω -> 
    S(m) ×ₙ k = k +ₙ (m ×ₙ k) -> S(m) ×ₙ S(k) = S(k) +ₙ (m ×ₙ S(k))) as P4.
  { intros k P4 P5.
    rewrite (multi_red _ _ (suc_is_nat _ P1) P4).
    rewrite (multi_red _ _ P1 P4).
    rewrite P5.
    rewrite (add_associative _ _ _ (suc_is_nat _ P1) P4 (multi_is_nat _ _ P1 P4)).
    rewrite (add_associative _ _ _ (suc_is_nat _ P4) P1 (multi_is_nat _ _ P1 P4)).
    rewrite (add_commutative _ _ (suc_is_nat _ P4) P1).
    rewrite (add_red _ _ P1 P4).
    rewrite (add_red_l _ _ P1 P4).
    reflexivity. }
  apply (induction_principle _ P3 P4 _ P2).
Qed.

Lemma distributive_l: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->
  m ×ₙ (n +ₙ p) = m ×ₙ n +ₙ m ×ₙ p.
Proof.
  intros m n p P1 P2 P3.
  assert (m ×ₙ (n +ₙ n.0) = m ×ₙ n +ₙ m ×ₙ n.0) as P4.
  { rewrite (add_zero _ P2).
    rewrite (multi_zero _ P1).
    rewrite (add_zero _ (multi_is_nat _ _ P1 P2)). 
    reflexivity. }
  assert (forall k, k ∈ ω -> m ×ₙ (n +ₙ k) = m ×ₙ n +ₙ m ×ₙ k -> 
    m ×ₙ (n +ₙ S(k)) = m ×ₙ n +ₙ m ×ₙ S(k)) as P5.
  { intros k P5 P6.
    rewrite (add_red _ _ P2 P5).
    rewrite (multi_red _ _ P1 (add_is_nat _ _ P2 P5)).
    rewrite P6.
    rewrite (multi_red _ _ P1 P5).
    rewrite (add_associative _ _ _ 
      (multi_is_nat _ _ P1 P2) P1 (multi_is_nat _ _ P1 P5)).
    rewrite (add_commutative _ _ (multi_is_nat _ _ P1 P2) P1).
    rewrite <- (add_associative _ _ _ 
      P1 (multi_is_nat _ _ P1 P2) (multi_is_nat _ _ P1 P5)).
    reflexivity. }
  apply (induction_principle _ P4 P5 _ P3).
Qed.

Lemma multi_commutative: forall m n, m ∈ ω -> n ∈ ω -> m ×ₙ n = n ×ₙ m.
Proof.
  intros m n P1 P2.
  assert (m ×ₙ n.0 = n.0 ×ₙ m) as P3.
  { rewrite (multi_zero _ P1).
    rewrite (multi_zero_l _ P1).
    reflexivity. }
  assert (forall k, k ∈ ω -> m ×ₙ k = k ×ₙ m -> m ×ₙ S(k) = S(k) ×ₙ m) as P4.
  { intros k P4 P5.
    rewrite (multi_red _ _ P1 P4).
    rewrite (multi_red_l _ _ P4 P1).
    f_equal.
    apply P5. }
  apply (induction_principle _ P3 P4 _ P2).
Qed.

Lemma multi_associative: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->
  m ×ₙ (n ×ₙ p) = (m ×ₙ n) ×ₙ p.
Proof.
  intros m n p P1 P2 P3.
  assert (m ×ₙ (n ×ₙ n.0) = (m ×ₙ n) ×ₙ n.0) as P4.
  { rewrite (multi_zero _ P2).
    rewrite (multi_zero _ P1).
    rewrite (multi_zero _ (multi_is_nat _ _ P1 P2)).
    reflexivity. }
  assert (forall k, k ∈ ω -> m ×ₙ (n ×ₙ k) = (m ×ₙ n) ×ₙ k ->
    m ×ₙ (n ×ₙ S(k)) = (m ×ₙ n) ×ₙ S(k)) as P5.
  { intros k P5 P6.
    rewrite (multi_red _ _ (multi_is_nat _ _ P1 P2) P5).
    rewrite <- P6.
    rewrite (multi_red _ _ P2 P5). 
    rewrite (distributive_l _ _ _ P1 P2 (multi_is_nat _ _ P2 P5)).
    reflexivity. }
  apply (induction_principle _ P4 P5 _ P3).
Qed.

Lemma multi_equal_zero: forall m n, m ∈ ω -> n ∈ ω ->
  m ×ₙ n = n.0 -> m = n.0 \/ n = n.0.
Proof.
  intros m n P1 P2.
  apply contraposition4.
  intros P3 P4.
  destruct (not_or_and _ _ P3) as [P5 P6].
  destruct (nat_is_suc _ P1 P5) as [mm [P7 P8]].
  destruct (nat_is_suc _ P2 P6) as [nn [P9 P10]].
  rewrite P8 in P4.
  rewrite (multi_red_l _ _ P7 P2) in P4.
  rewrite P10 in P4.
  rewrite (add_red_l _ _ P9 (multi_is_nat _ _ P7 (suc_is_nat _ P9))) in P4.
  absurd (n.0 = S( nn +ₙ mm ×ₙ S( nn))).
  + apply empty_not_suc.
  + symmetry.
    apply P4.
Qed.

Lemma add_equation: forall a b c d, a = b -> c = d -> a +ₙ c = b +ₙ d.
Proof.
  intros a b c d P1 P2.
  rewrite P1.
  rewrite P2.
  reflexivity.
Qed.

Lemma add_cancellation: forall m n l, m ∈ ω -> n ∈ ω -> l ∈ ω ->
  m +ₙ l = n +ₙ l -> m = n.
Proof.
  intros m n l P1 P2 P3 P4.
  pose (P := fun k => m +ₙ k = n +ₙ k -> m = n).
  assert (P n.0) as I1.
  { intros Q1.
    rewrite (add_zero _ P1) in Q1.
    rewrite (add_zero _ P2) in Q1.
    apply Q1. }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 Q3.
    rewrite (add_red _ _ P1 Q1) in Q3.
    rewrite (add_red _ _ P2 Q1) in Q3.
    apply (Q2 (suc_unique _ _ 
      (add_is_nat _ _ P1 Q1) (add_is_nat _ _ P2 Q1) Q3)). }
  apply (induction_principle _ I1 I2 _ P3 P4).
Qed.

Lemma add_cancellation_2: forall m n p q, p = q -> m +ₙ p = n +ₙ q -> 
  m ∈ ω -> n ∈ ω -> p ∈ ω -> q ∈ ω -> m = n.
Proof.
  intros m n p q P1 P2 P3 P4 P5 P6.
  rewrite P1 in P2.
  apply (add_cancellation _ _ _ P3 P4 P6 P2).
Qed.

Lemma add_cancellation_inverse: forall m n l, m = n -> m +ₙ l = n +ₙ l.
Proof.
  intros m n l P1.
  rewrite P1.
  reflexivity.
Qed.

Lemma multi_equation: forall a b c d, a = b -> c = d -> a ×ₙ c = b ×ₙ d.
Proof.
  intros a b c d P1 P2.
  rewrite P1.
  rewrite P2.
  reflexivity.
Qed.

Lemma multi_equation_2: forall a b c, a = b -> a ×ₙ c = b ×ₙ c.
Proof.
  intros a b c P1.
  rewrite P1.
  reflexivity.
Qed.

Lemma add_cyc: forall m n l, m ∈ ω -> n ∈ ω -> l ∈ ω -> 
  (m +ₙ n) +ₙ l = (m +ₙ l) +ₙ n.
Proof.
  intros m n l P1 P2 P3.
  rewrite <- (add_associative _ _ _ P1 P3 P2).
  rewrite (add_commutative _ _ P3 P2).
  rewrite (add_associative _ _ _ P1 P2 P3).
  reflexivity.
Qed.
(*----------------------------------------------------------------------------*)

(* Order *)
(* TODO Change nat k into k ∈ ω *)
Definition less (m: set) (n: set) := m ∈ n.
Notation "m <ₙ n" := (less m n) (at level 65, no associativity).

Definition less_equal (m: set) (n: set) := (less m n) \/ (m = n).
Notation "m ≤ₙ n" := (less_equal m n) (at level 65, no associativity).

Lemma in_suc: forall m n, nat n -> m ∈ S(n) -> m ∈ n \/ m = n.
Proof.
  intros m n P2 P3.
  destruct (in_union2_in _ _ _ P3) as [P4|P4].
  + left.
    apply P4.
  + right.
    symmetry.   
    apply (in_singleton_equal _ _ P4).
Qed.

Lemma in_nat_nat: forall m n, nat n -> m ∈ n -> nat m.
Proof.
  intros m n P1 P2.
  assert (forall m1, m1 ∈ n.0 -> nat m1) as P3.
  { intros m1 Q1.
    absurd (m1 ∈ n.0).
    + apply not_in_empty.
    + apply Q1. }
  assert (forall k, k ∈ ω -> (forall m1, m1 ∈ k -> nat m1) -> 
    (forall m1, m1 ∈ S(k) -> nat m1)) as P4.
  { intros k Q1 Q2 m1 Q3.
    destruct (in_suc _ _ (omega_elim _ Q1) Q3) as [Q4|Q4].
    + apply (Q2 _ Q4).
    + rewrite Q4.
      apply (omega_elim _ Q1). }
  apply (induction_principle _ P3 P4 _ (omega_intro _ P1) _ P2).
Qed.

Lemma suc_less: forall m n, nat m -> nat n -> m <ₙ n -> S(m) <ₙ S(n).
Proof.
  intros m n P1 P2 P3.
  assert (forall m, m <ₙ n.0 -> S(m) <ₙ S(n.0)) as P4.
  { intros m1 Q1.
    absurd (m1 <ₙ n.0).
    + apply not_in_empty.
    + apply Q1. }
  assert (forall k, k ∈ ω -> (forall m1, m1 <ₙ k -> S(m1) <ₙ S(k)) ->
    (forall m2, m2 <ₙ S(k) -> S(m2) <ₙ S(S(k)))) as P5.
  { intros k Q1 Q2 m2 Q3.
    destruct (in_suc _ _ (omega_elim _ Q1) Q3) as [Q4|Q4].
    + pose (nat_is_trans _ (suc_is_nat _ (suc_is_nat _ Q1))) as Q5.
      apply (Q5 _ _ (Q2 _ Q4) (suc_intro_1 (S(k)))).
    + rewrite Q4.
      apply suc_intro_1. }
  apply (induction_principle _ P4 P5 _ (omega_intro _ P2) _ P3).
Qed.

Lemma empty_in_nat: forall n, nat n -> n <> n.0 -> n.0 ∈ n.
Proof.
  intros n P1 P2.
  pose (fun k => nat k -> k <> n.0 -> n.0 ∈ k) as P.
  assert (P (n.0)) as P3.
  { intros Q1 Q2.
    contradiction. }
  assert (forall k, k ∈ ω -> P k -> P (S(k))) as P4.
  { intros k Q1 Q2 Q3 Q4.
    destruct (LEM (k = n.0)) as [Q5|Q5].
    + rewrite Q5.
      apply suc_intro_1.
    + pose (nat_is_trans _ (suc_is_nat _ Q1)) as Q6.
      apply (Q6 _ _ (Q2 (omega_elim _ Q1) Q5) (suc_intro_1 k)). }
  apply (induction_principle _ P3 P4 _ (omega_intro _ P1) P1 P2).
Qed.
    
Theorem trichotomy_of_nat: forall m n, nat m -> nat n ->
  ((m <ₙ n) /\ ~(m = n) /\ ~(n <ₙ m)) \/
  (~(m <ₙ n) /\ (m = n) /\ ~(n <ₙ m)) \/
  (~(m <ₙ n) /\ ~(m = n) /\ (n <ₙ m)).
Proof.
  intros m n P1 P2.
  pose (fun k => nat k -> k ∈ n \/ k = n \/ n ∈ k) as P.
  assert (P (n.0)) as P3.
  { intros Q1.
    destruct (LEM (n = n.0)) as [Q2|Q2].
    + right. left.
      symmetry.
      apply Q2.
    + left.
      apply (empty_in_nat _ P2 Q2). }
  assert (forall k, k ∈ ω -> P k -> P (S(k))) as P4.
  { intros k Q1 Q2 Q3.
    pose (in_nat_nat _ _ Q3 (suc_intro_1 k)) as Q4.
    destruct (Q2 Q4) as [Q5|[Q5|Q5]].
    + destruct (suc_elim _ _ (suc_less _ _ Q4 P2 Q5)) as [Q6|Q6].
      - right. left.
        apply Q6.
      - left.
        apply Q6.
    + right. right.
      rewrite Q5.
      apply suc_intro_1.
    + right. right.
      apply (nat_is_trans _ (omega_intro _ Q3) _ _ Q5 (suc_intro_1 k)). }
  destruct (induction_principle _ P3 P4 _ (omega_intro _ P1) P1) as [P5|[P5|P5]].
  + left.
    split.
    { apply P5. }
    split.
    { intros P6.
      rewrite P6 in P5.
      absurd (n ∈ n).
      + apply (nat_not_in_self _ (omega_intro _ P2)).
      + apply P5. }
    { intros P6.
      absurd (n ∈ n).
      + apply (nat_not_in_self _ (omega_intro _ P2)).
      + apply (nat_is_trans _ (omega_intro _ P2) _ _ P6 P5). }
  + right. left.
    split. 
    { rewrite P5.
      apply (nat_not_in_self _ (omega_intro _ P2)). }
    split.
    { apply P5. }
    { rewrite P5.
      apply (nat_not_in_self _ (omega_intro _ P2)). }
  + right. right.
    split.
    { intros P6.
      absurd (n ∈ n).
      + apply (nat_not_in_self _ (omega_intro _ P2)).
      + apply (nat_is_trans _ (omega_intro _ P2) _ _ P5 P6). }
    split.
    { intros P6.
      rewrite P6 in P5.
      absurd (n ∈ n).
      + apply (nat_not_in_self _ (omega_intro _ P2)).
      + apply P5. }
    { apply P5. }
Qed.

Theorem trichotomy_of_nat_weak: forall m n, nat m -> nat n ->
  (m <ₙ n) \/ (m = n) \/ (n <ₙ m).
Proof. 
  intros m n P1 P2.
  destruct (trichotomy_of_nat _ _ P1 P2) as [[P3 _]|[[_ [P3 _]]|[_ [_ P3]]]]. 
  + left. 
    apply P3.
  + right. left.
    apply P3.
  + right. right.
    apply P3.
Qed.
(*----------------------------------------------------------------------------*)

(* Ltac *)
(* Flow: add enough equation into the goal *)
(*       run nat_normal_form to normalize it *)
(*       exchange order of multiple (I don't know how to do it automaticly now) *)
(*       run nat_rea to reduce result *)
(*       run is_nat to clean up *)
Ltac is_nat :=
  repeat match goal with
    | [       |- ?P = ?P         ] => reflexivity
    | [ H: ?P |- ?P              ] => apply H
    | [       |- ⟨_, _⟩ ∈ cp _ _ ] => apply cp_intro
    | [       |- ?P +ₙ ?Q ∈ ω    ] => apply add_is_nat
    | [       |- ?P ×ₙ ?Q ∈ ω    ] => apply multi_is_nat
  end.

Ltac nat_unwrap_multi_ M :=
  repeat match M with
    | ?R ×ₙ (?P +ₙ ?Q) => rewrite (distributive_l R P Q)
    | (?P +ₙ ?Q) ×ₙ ?R => rewrite (multi_commutative (P +ₙ Q) R)
    | ?P ×ₙ (?Q ×ₙ ?R) => rewrite (multi_commutative P (Q ×ₙ R))
    | ?P ×ₙ ?Q         => nat_unwrap_multi_ P; nat_unwrap_multi_ Q
    | ?P +ₙ ?Q         => nat_unwrap_multi_ P; nat_unwrap_multi_ Q
  end.

Ltac nat_unwrap_multi :=
  repeat match goal with
    | [ |- ?P = ?Q ] => nat_unwrap_multi_ P; nat_unwrap_multi_ Q
  end.

Ltac nat_unwrap_add_ M :=
  repeat match M with
    | ?P +ₙ (?Q +ₙ ?R) => rewrite (add_associative P Q R)
    | ?P +ₙ ?Q         => nat_unwrap_add_ P
  end.

Ltac nat_unwrap_add :=
  repeat match goal with
    | [ |- ?P = ?Q ] => nat_unwrap_add_ P; nat_unwrap_add_ Q
  end.

Ltac nat_normal_form :=
  nat_unwrap_multi;
  nat_unwrap_add.

Ltac nat_red_ M P :=
  repeat match M with
    (*| P              => assumption*)
    (*| _ +ₙ P         => assumption [>do nothing<]*)
    | P +ₙ ?Q        => rewrite (add_commutative P Q)
    | (?R +ₙ P) +ₙ ?Q => rewrite (add_cyc R P Q)
    | ?Q +ₙ _        => nat_red_ Q P
  end.

Ltac nat_red :=
  repeat match goal with
    | [ |- ?P               = ?P      ] => reflexivity
    | [ |- _          +ₙ ?P = _ +ₙ ?P ] => apply add_cancellation_inverse
    | [ |- ?P         +ₙ ?Q = _ +ₙ ?P ] => rewrite (add_commutative P Q)
    | [ |- (?R +ₙ ?P) +ₙ ?Q = _ +ₙ ?P ] => rewrite (add_cyc R P Q)
    | [ |- ?R         +ₙ _  = _ +ₙ ?P ] => repeat nat_red_ R P
  end.


Lemma test: forall a b c d, a ∈ ω -> b ∈ ω -> c ∈ ω -> d ∈ ω ->
  (a ×ₙ b) +ₙ a ×ₙ (c +ₙ d) ×ₙ (a +ₙ b) = a ×ₙ (c +ₙ d) ×ₙ (a +ₙ b) +ₙ (a ×ₙ b).
Proof.
  intros a b c d P1 P2 P3 P4.
  nat_normal_form.
  nat_red.
  all: is_nat.
Qed.
(*----------------------------------------------------------------------------*)
