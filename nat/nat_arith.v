Require Import axiom.axiom.
Require Import axiom.logic.
Require Import operation.basic.
Require Import relation.relation.
Require Import relation.function.
Require Import relation.util_function.
Require Import nat.inductive.
Require Import nat.nat.
Require Import nat.recursion.

(* Arithmetic *)
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
          + apply (suc_in_omega _ P2). }
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
      * apply (suc_in_omega _ P1).
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
    
Notation "m ₙ+ n" := ((add_proto m)[n]) (at level 65, no associativity).

Notation "ₙ0" := ∅       (at level 60, no associativity).
Notation "ₙ1" := (S(ₙ0)) (at level 60, no associativity).
Notation "ₙ2" := (S(ₙ1)) (at level 60, no associativity).
Notation "ₙ3" := (S(ₙ2)) (at level 60, no associativity).
Notation "ₙ4" := (S(ₙ3)) (at level 60, no associativity).

Lemma add_zero: forall m, m ∈ ω -> m ₙ+ ₙ0 = m.
Proof.
  intros m P1.
  apply (add_proto_elim_1 _ P1).
Qed.

Lemma add_red: forall m n, m ∈ ω -> n ∈ ω -> m ₙ+ S(n) = S(m ₙ+ n).
Proof.
  intros m n P1 P2.
  apply (add_proto_elim_2 _ _ P1 P2).
Qed.

Lemma add_in_omega: forall m n, m ∈ ω -> n ∈ ω -> m ₙ+ n ∈ ω.
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

Theorem one_one_two: ₙ1 ₙ+ ₙ1 = ₙ2.
Proof.
  assert (ₙ1 ∈ ω) as P1.
  { apply suc_in_omega. 
    apply empty_in_omega. }
  rewrite (add_red (ₙ1) (ₙ0) P1 empty_in_omega).
  rewrite (add_zero (ₙ1) P1).
  reflexivity.
Qed.

Definition multi_proto (m: set) :=
  extract_set (recursion_theorem ω (ₙ0) (add_proto m)).

Lemma multi_proto_is_function: forall m, m ∈ ω -> fover (multi_proto m) ω ω.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω (ₙ0) (add_proto m)) 
    (empty_in_omega) (add_proto_is_function _ P1)) as [P2 _].
  apply P2.
Qed.

Lemma multi_proto_elim_1: forall m, m ∈ ω -> (multi_proto m)[∅] = ∅.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω (ₙ0) (add_proto m)) 
    (empty_in_omega) (add_proto_is_function _ P1)) as [_ [P2 _]].
  apply P2.
Qed.

Lemma multi_proto_elim_2: forall m n, m ∈ ω -> n ∈ ω -> 
    (multi_proto m)[S(n)] = (add_proto m)[(multi_proto m)[n]].
Proof.
  intros m n P1 P2.
  destruct (extract_set_property (recursion_theorem ω (ₙ0) (add_proto m)) 
    (empty_in_omega) (add_proto_is_function _ P1)) as [_ [_ P3]].
  apply (P3 _ P2).
Qed.
    
Notation "m ₙx n" := ((multi_proto m)[n]) (at level 64, no associativity).

Lemma multi_zero: forall m, m ∈ ω -> m ₙx ₙ0 = ₙ0.
Proof.
  intros m P1.
  apply (multi_proto_elim_1 _ P1).
Qed.

Lemma multi_red: forall m n, m ∈ ω -> n ∈ ω -> m ₙx S(n) = m ₙ+ (m ₙx n).
Proof.
  intros m n P1 P2.
  apply (multi_proto_elim_2 _ _ P1 P2).
Qed.

Lemma multi_in_omega: forall m n, m ∈ ω -> n ∈ ω -> m ₙx n ∈ ω.
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

Lemma one_in_omega: ₙ1 ∈ ω.
Proof.
  apply (suc_in_omega _ empty_in_omega).
Qed.

Definition exp_proto (m: set) :=
  extract_set (recursion_theorem ω (ₙ1) (multi_proto m)).

Lemma exp_proto_is_function: forall m, m ∈ ω -> fover (exp_proto m) ω ω.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω (ₙ1) (multi_proto m)) 
    (one_in_omega) (multi_proto_is_function _ P1)) as [P2 _].
  apply P2.
Qed.

Lemma exp_proto_elim_1: forall m, m ∈ ω -> (exp_proto m)[∅] = ₙ1.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω (ₙ1) (multi_proto m)) 
    (one_in_omega) (multi_proto_is_function _ P1)) as [_ [P2 _]].
  apply P2.
Qed.

Lemma exp_proto_elim_2: forall m n, m ∈ ω -> n ∈ ω -> 
    (exp_proto m)[S(n)] = (multi_proto m)[(exp_proto m)[n]].
Proof.
  intros m n P1 P2.
  destruct (extract_set_property (recursion_theorem ω (ₙ1) (multi_proto m)) 
    (one_in_omega) (multi_proto_is_function _ P1)) as [_ [_ P3]].
  apply (P3 _ P2).
Qed.
    
Notation "m ₙ^ n" := ((exp_proto m)[n]) (at level 65, no associativity).

Lemma exp_zero: forall m, m ∈ ω -> m ₙ^ ₙ0 = ₙ1.
Proof.
  intros m P1.
  apply (exp_proto_elim_1 _ P1).
Qed.

Lemma exp_red: forall m n, m ∈ ω -> n ∈ ω -> m ₙ^ S(n) = m ₙx (m ₙ^ n).
Proof.
  intros m n P1 P2.
  apply (exp_proto_elim_2 _ _ P1 P2).
Qed.

Lemma add_zero_l: forall m, m ∈ ω -> ₙ0 ₙ+ m = m.
Proof.
  intros m P1.
  assert (ₙ0 ₙ+ ₙ0 = ₙ0) as P2.
  { apply (add_zero _ empty_in_omega). }
  assert (forall k, k ∈ ω -> ₙ0 ₙ+ k = k -> ₙ0 ₙ+ S(k) = S(k)) as P3.
  { intros k P3 P4.
    rewrite (add_red _ _ empty_in_omega P3).
    f_equal.
    apply P4. }
  apply (induction_principle _ P2 P3 _ P1).
Qed.

Lemma add_red_l: forall m n, m ∈ ω -> n ∈ ω -> S(m) ₙ+ n = S(m ₙ+ n).
Proof.
  intros m n P1 P2.
  assert (S(m) ₙ+ ₙ0 = S(m ₙ+ ₙ0)) as P3.
  { rewrite (add_zero _ (suc_in_omega _ P1)).
    rewrite (add_zero _ P1).
    reflexivity. }
  assert (forall k, k ∈ ω -> 
    S(m) ₙ+ k = S(m ₙ+ k) -> S(m) ₙ+ S(k) = S(m ₙ+ S(k))) as P4.
  { intros k P4 P5.
    rewrite (add_red _ _ (suc_in_omega _ P1) P4).
    rewrite P5.
    f_equal.
    symmetry.
    apply (add_red _ _ P1 P4). }
  apply (induction_principle _ P3 P4 _ P2).
Qed.

Lemma add_commutative: forall m n, m ∈ ω -> n ∈ ω -> m ₙ+ n = n ₙ+ m.
Proof. 
  intros m n P1 P2.
  assert (m ₙ+ ₙ0 = ₙ0 ₙ+ m) as P3.
  { rewrite (add_zero _ P1).
    rewrite (add_zero_l _ P1).
    reflexivity. }
  assert (forall k, k ∈ ω -> m ₙ+ k = k ₙ+ m -> m ₙ+ S(k) = S(k) ₙ+ m) as P4.
  { intros k P4 P5.
    rewrite (add_red _ _ P1 P4).
    rewrite (add_red_l _ _ P4 P1).
    f_equal.
    apply P5. }
  apply (induction_principle _ P3 P4 _ P2).
Qed.

Lemma add_associative: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->
  m ₙ+ (n ₙ+ p) = (m ₙ+ n) ₙ+ p.
Proof.
  intros m n p P1 P2 P3.
  assert (m ₙ+ (n ₙ+ ₙ0) = (m ₙ+ n) ₙ+ ₙ0) as P4.
  { rewrite (add_zero _ P2).
    symmetry.    
    apply add_zero.
    apply (add_in_omega _ _ P1 P2). }
  assert (forall k, k ∈ ω -> m ₙ+ (n ₙ+ k) = (m ₙ+ n) ₙ+ k ->
    m ₙ+ (n ₙ+ S(k)) = (m ₙ+ n) ₙ+ S(k)) as P5.
  { intros k P5 P6.
    rewrite (add_red _ _ (add_in_omega _ _ P1 P2) P5).
    rewrite <- P6.
    rewrite <- (add_red _ _ P1 (add_in_omega _ _ P2 P5)).
    rewrite <- (add_red _ _ P2 P5).
    reflexivity. }
  apply (induction_principle _ P4 P5 _ P3).
Qed.

Lemma multi_zero_l: forall m, m ∈ ω -> ₙ0 ₙx m = ₙ0.
Proof.
  intros m P1.
  assert (ₙ0 ₙx ₙ0 = ₙ0) as P2.
  { apply (multi_zero _ empty_in_omega). }
  assert (forall k, k ∈ ω -> ₙ0 ₙx k = ₙ0 -> ₙ0 ₙx S(k) = ₙ0) as P3.
  { intros k P3 P4.
    rewrite (multi_red _ _ empty_in_omega P3).
    rewrite P4.
    apply (add_zero _ empty_in_omega). }
  apply (induction_principle _ P2 P3 _ P1).
Qed.

Lemma multi_red_l: forall m n, m ∈ ω -> n ∈ ω -> S(m) ₙx n = n ₙ+ (m ₙx n).
Proof.
  intros m n P1 P2.
  assert (S(m) ₙx ₙ0 = ₙ0 ₙ+ (m ₙx ₙ0)) as P3.
  { rewrite (multi_zero _ (suc_in_omega _ P1)).
    rewrite (multi_zero _ P1).
    rewrite (add_zero _ empty_in_omega).
    reflexivity. }
  assert (forall k, k ∈ ω -> 
    S(m) ₙx k = k ₙ+ (m ₙx k) -> S(m) ₙx S(k) = S(k) ₙ+ (m ₙx S(k))) as P4.
  { intros k P4 P5.
    rewrite (multi_red _ _ (suc_in_omega _ P1) P4).
    rewrite (multi_red _ _ P1 P4).
    rewrite P5.
    rewrite (add_associative _ _ _ (suc_in_omega _ P1) P4 (multi_in_omega _ _ P1 P4)).
    rewrite (add_associative _ _ _ (suc_in_omega _ P4) P1 (multi_in_omega _ _ P1 P4)).
    rewrite (add_commutative _ _ (suc_in_omega _ P4) P1).
    rewrite (add_red _ _ P1 P4).
    rewrite (add_red_l _ _ P1 P4).
    reflexivity. }
  apply (induction_principle _ P3 P4 _ P2).
Qed.

Lemma distributive_l: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->
  m ₙx (n ₙ+ p) = m ₙx n ₙ+ m ₙx p.
Proof.
  intros m n p P1 P2 P3.
  assert (m ₙx (n ₙ+ ₙ0) = m ₙx n ₙ+ m ₙx ₙ0) as P4.
  { rewrite (add_zero _ P2).
    rewrite (multi_zero _ P1).
    rewrite (add_zero _ (multi_in_omega _ _ P1 P2)). 
    reflexivity. }
  assert (forall k, k ∈ ω -> m ₙx (n ₙ+ k) = m ₙx n ₙ+ m ₙx k -> 
    m ₙx (n ₙ+ S(k)) = m ₙx n ₙ+ m ₙx S(k)) as P5.
  { intros k P5 P6.
    rewrite (add_red _ _ P2 P5).
    rewrite (multi_red _ _ P1 (add_in_omega _ _ P2 P5)).
    rewrite P6.
    rewrite (multi_red _ _ P1 P5).
    rewrite (add_associative _ _ _ 
      (multi_in_omega _ _ P1 P2) P1 (multi_in_omega _ _ P1 P5)).
    rewrite (add_commutative _ _ (multi_in_omega _ _ P1 P2) P1).
    rewrite <- (add_associative _ _ _ 
      P1 (multi_in_omega _ _ P1 P2) (multi_in_omega _ _ P1 P5)).
    reflexivity. }
  apply (induction_principle _ P4 P5 _ P3).
Qed.

Lemma multi_commutative: forall m n, m ∈ ω -> n ∈ ω -> m ₙx n = n ₙx m.
Proof.
  intros m n P1 P2.
  assert (m ₙx ₙ0 = ₙ0 ₙx m) as P3.
  { rewrite (multi_zero _ P1).
    rewrite (multi_zero_l _ P1).
    reflexivity. }
  assert (forall k, k ∈ ω -> m ₙx k = k ₙx m -> m ₙx S(k) = S(k) ₙx m) as P4.
  { intros k P4 P5.
    rewrite (multi_red _ _ P1 P4).
    rewrite (multi_red_l _ _ P4 P1).
    f_equal.
    apply P5. }
  apply (induction_principle _ P3 P4 _ P2).
Qed.

Lemma multi_associative: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->
  m ₙx (n ₙx p) = (m ₙx n) ₙx p.
Proof.
  intros m n p P1 P2 P3.
  assert (m ₙx (n ₙx ₙ0) = (m ₙx n) ₙx ₙ0) as P4.
  { rewrite (multi_zero _ P2).
    rewrite (multi_zero _ P1).
    rewrite (multi_zero _ (multi_in_omega _ _ P1 P2)).
    reflexivity. }
  assert (forall k, k ∈ ω -> m ₙx (n ₙx k) = (m ₙx n) ₙx k ->
    m ₙx (n ₙx S(k)) = (m ₙx n) ₙx S(k)) as P5.
  { intros k P5 P6.
    rewrite (multi_red _ _ (multi_in_omega _ _ P1 P2) P5).
    rewrite <- P6.
    rewrite (multi_red _ _ P2 P5). 
    rewrite (distributive_l _ _ _ P1 P2 (multi_in_omega _ _ P2 P5)).
    reflexivity. }
  apply (induction_principle _ P4 P5 _ P3).
Qed.

Lemma multi_equal_zero: forall m n, m ∈ ω -> n ∈ ω ->
  m ₙx n = ₙ0 -> m = ₙ0 \/ n = ₙ0.
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
  rewrite (add_red_l _ _ P9 (multi_in_omega _ _ P7 (suc_in_omega _ P9))) in P4.
  absurd (ₙ0 = S( nn ₙ+ mm ₙx S( nn))).
  + apply empty_not_suc.
  + symmetry.
    apply P4.
Qed.

Definition less (m: set) (n: set) := m ∈ n.
Notation "m ₙ< n" := (less m n) (at level 65, no associativity).

Definition less_equal (m: set) (n: set) := (less m n) \/ (m = n).
Notation "m ₙ≤ n" := (less_equal m n) (at level 65, no associativity).

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
  assert (forall m1, m1 ∈ ₙ0 -> nat m1) as P3.
  { intros m1 Q1.
    absurd (m1 ∈ ₙ0).
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

Lemma suc_less: forall m n, nat m -> nat n -> m ₙ< n -> S(m) ₙ< S(n).
Proof.
  intros m n P1 P2 P3.
  assert (forall m, m ₙ< ₙ0 -> S(m) ₙ< S(ₙ0)) as P4.
  { intros m1 Q1.
    absurd (m1 ₙ< ₙ0).
    + apply not_in_empty.
    + apply Q1. }
  assert (forall k, k ∈ ω -> (forall m1, m1 ₙ< k -> S(m1) ₙ< S(k)) ->
    (forall m2, m2 ₙ< S(k) -> S(m2) ₙ< S(S(k)))) as P5.
  { intros k Q1 Q2 m2 Q3.
    destruct (in_suc _ _ (omega_elim _ Q1) Q3) as [Q4|Q4].
    + pose (nat_is_trans _ (omega_elim _ (suc_in_omega _ (suc_in_omega _ Q1)))) as Q5.
      apply (Q5 _ _ (Q2 _ Q4) (suc_intro_1 (S(k)))).
    + rewrite Q4.
      apply suc_intro_1. }
  apply (induction_principle _ P4 P5 _ (omega_intro _ P2) _ P3).
Qed.

Lemma empty_in_nat: forall n, nat n -> n <> ₙ0 -> ₙ0 ∈ n.
Proof.
  intros n P1 P2.
  pose (fun k => nat k -> k <> ₙ0 -> ₙ0 ∈ k) as P.
  assert (P (ₙ0)) as P3.
  { intros Q1 Q2.
    contradiction. }
  assert (forall k, k ∈ ω -> P k -> P (S(k))) as P4.
  { intros k Q1 Q2 Q3 Q4.
    destruct (LEM (k = ₙ0)) as [Q5|Q5].
    + rewrite Q5.
      apply suc_intro_1.
    + pose (nat_is_trans _ (omega_elim _ (suc_in_omega _ Q1))) as Q6.
      apply (Q6 _ _ (Q2 (omega_elim _ Q1) Q5) (suc_intro_1 k)). }
  apply (induction_principle _ P3 P4 _ (omega_intro _ P1) P1 P2).
Qed.
    
Theorem trichotomy_of_nat: forall m n, nat m -> nat n ->
  ((m ₙ< n) /\ ~(m = n) /\ ~(n ₙ< m)) \/
  (~(m ₙ< n) /\ (m = n) /\ ~(n ₙ< m)) \/
  (~(m ₙ< n) /\ ~(m = n) /\ (n ₙ< m)).
Proof.
  intros m n P1 P2.
  pose (fun k => nat k -> k ∈ n \/ k = n \/ n ∈ k) as P.
  assert (P (ₙ0)) as P3.
  { intros Q1.
    destruct (LEM (n = ₙ0)) as [Q2|Q2].
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
      apply (nat_is_trans _ Q3 _ _ Q5 (suc_intro_1 k)). }
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
      + apply (nat_is_trans _ P2 _ _ P6 P5). }
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
      + apply (nat_is_trans _ P2 _ _ P5 P6). }
    split.
    { intros P6.
      rewrite P6 in P5.
      absurd (n ∈ n).
      + apply (nat_not_in_self _ (omega_intro _ P2)).
      + apply P5. }
    { apply P5. }
Qed.

Theorem trichotomy_of_nat_weak: forall m n, nat m -> nat n ->
  (m ₙ< n) \/ (m = n) \/ (n ₙ< m).
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
