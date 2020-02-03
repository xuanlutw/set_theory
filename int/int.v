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

Definition int_ctor_rel := 
  subset_ctor (fun x => 
    exists a b c d, x = ⟨⟨a, b⟩, ⟨c, d⟩⟩ /\ a +ₙ d = b +ₙ c)
    (cp (cp ω ω) (cp ω ω)).

Lemma int_ctor_rel_refl: r_refl int_ctor_rel (cp ω ω).
Proof.
  intros x P1.
  apply subset_intro.
  + apply cp_intro.
    - apply P1.
    - apply P1.
  + destruct (cp_elim _ _ _ P1) as [a [b [P2 [P3 P4]]]].
    exists a.
    exists b.
    exists a.
    exists b.
    split.
    - rewrite P4.
      reflexivity.
    - apply (add_commutative _ _ P2 P3).
Qed.

Lemma int_ctor_rel_sym: r_sym int_ctor_rel.
Proof.
  intros x y P1.
  apply subset_intro.
  + apply cp_swap.
    apply (subset_elim_2 _ _ _ P1).
  + destruct (subset_elim _ _ _ P1) as [P2 [a [b [c [d [P3 P4]]]]]]. 
    exists c. exists d. exists a. exists b.
    split.
    - apply (opair_equal_swap _ _ _ _ P3).
    - destruct (cp_elim_2 _ _ _ _ P2) as [P5 P6].
      rewrite (opair_equal_elim_fst _ _ _ _ P3) in P5.
      rewrite (opair_equal_elim_snd _ _ _ _ P3) in P6.
      destruct (cp_elim_2 _ _ _ _ P5) as [Q1 Q2]. 
      destruct (cp_elim_2 _ _ _ _ P6) as [Q3 Q4]. 
      rewrite (add_commutative _ _ Q3 Q2).
      rewrite (add_commutative _ _ Q4 Q1).
      symmetry.
      apply P4.
Qed.
    
Lemma int_ctor_rel_trans: r_trans int_ctor_rel.
Proof.
  intros x y z P1 P2.
  apply subset_intro.
  + apply cp_intro.
    - destruct (subset_elim _ _ _ P1) as [P3 _].
      destruct (cp_elim_2 _ _ _ _ P3) as [P4 _].
      apply P4.
    - destruct (subset_elim _ _ _ P2) as [P3 _].
      destruct (cp_elim_2 _ _ _ _ P3) as [_ P4].
      apply P4.
  + destruct (subset_elim _ _ _ P1) as [Q1 [a1 [a2 [a3 [a4 [Q2 Q3]]]]]]. 
    destruct (subset_elim _ _ _ P2) as [R1 [b1 [b2 [b3 [b4 [R2 R3]]]]]]. 
    exists a1. exists a2. exists b3. exists b4. 
    split.
    - rewrite (opair_equal_elim_fst _ _ _ _ Q2).
      rewrite (opair_equal_elim_snd _ _ _ _ R2).
      reflexivity.
    - rewrite Q2 in Q1.
      destruct (cp_elim_2 _ _ _ _ Q1) as [Q4 Q5].
      destruct (cp_elim_2 _ _ _ _ Q4) as [Q6 Q7].
      destruct (cp_elim_2 _ _ _ _ Q5) as [Q8 Q9].
      rewrite R2 in R1.
      destruct (cp_elim_2 _ _ _ _ R1) as [_ R5].
      destruct (cp_elim_2 _ _ _ _ R5) as [R6 R7].
      pose (opair_equal_elim_snd _ _ _ _ Q2) as P3.
      rewrite (opair_equal_elim_fst _ _ _ _ R2) in P3.
      pose (add_equation _ _ _ _ Q3 R3) as P4.
      rewrite (opair_equal_elim_fst _ _ _ _ P3) in P4.
      rewrite (opair_equal_elim_snd _ _ _ _ P3) in P4.
      rewrite (add_commutative _ _ Q9 R6) in P4.
      rewrite (add_associative _ _ _ (add_is_nat _ _ Q7 Q8) R6 Q9) in P4.
      rewrite (add_commutative _ _ (add_is_nat _ _ Q6 Q9) (add_is_nat _ _ Q8 R7)) in P4.
      rewrite (add_associative _ _ _ (add_is_nat _ _ Q8 R7) Q6 Q9) in P4.
      pose ((add_cancellation _ _ _ 
        (add_is_nat _ _ (add_is_nat _ _ Q8 R7) Q6)
        (add_is_nat _ _ (add_is_nat _ _ Q7 Q8) R6) Q9) P4) as P5.
      rewrite <- (add_associative _ _ _ Q8 R7 Q6) in P5.
      rewrite (add_commutative _ _ Q8 (add_is_nat _ _ R7 Q6)) in P5.
      rewrite (add_commutative _ _ R7 Q6) in P5.
      rewrite (add_commutative _ _ Q7 Q8) in P5.
      rewrite <- (add_associative _ _ _ Q8 Q7 R6) in P5.
      rewrite (add_commutative _ _ Q8 (add_is_nat _ _ Q7 R6)) in P5.
      apply ((add_cancellation _ _ _ 
        (add_is_nat _ _ Q6 R7)
        (add_is_nat _ _ Q7 R6) Q8) P5).
Qed.

Lemma int_ctor_rel_is_equiv_rel: equiv_rel int_ctor_rel (cp ω ω).
Proof.
  split. split.
  + apply cp_subset_rel.
  + split.
    - apply (cp_subset_dom _ _ (cp ω ω)).
      apply (subset_elim_2).
    - apply (cp_subset_ran _ (cp ω ω) _).
      apply (subset_elim_2).
  + split.
    - apply int_ctor_rel_refl. 
    - split.
      * apply int_ctor_rel_sym.
      * apply int_ctor_rel_trans.
Qed.

Definition ℤ := (cp ω ω)[\ int_ctor_rel].

Definition int_ctor (m: set) (n: set) :=
  (cp ω ω)[int_ctor_rel, ⟨m, n⟩].

Lemma int_elim: forall x, x ∈ ℤ -> exists m n, 
  m ∈ ω /\ n ∈ ω /\ x = (int_ctor m n).
Proof.
  intros x P1.
  destruct (equiv_part_elim_1 _ _ _ P1) as [s [P2 P3]].
  destruct (cp_elim _ _ _ P2) as [m [n [P4 [P5 P6]]]].
  exists m. exists n.
  split.
  + apply P4.
  + split.
    - apply P5.
    - rewrite P6 in P3.
      apply P3.
Qed.

Lemma int_elim_fst: forall m n, int_ctor m n ∈ ℤ -> m ∈ ω.
Proof.
  intros m n P1.
  destruct (int_elim _ P1) as [m2 [n2 [P2 [P3 P4]]]].
  symmetry in P4.
  pose (equiv_class_eq_elim _ _ _ _ 
    int_ctor_rel_is_equiv_rel (cp_intro _ _ _ _ P2 P3) P4) as P5.
  pose (equiv_rel_elim_2 _ _ _ _ int_ctor_rel_is_equiv_rel P5) as P6.
  destruct (cp_elim_2 _ _ _ _ P6) as [P7 _].
  apply P7.
Qed.

Lemma int_equal_elim: forall m1 n1 m2 n2, m1 ∈ ω -> n1 ∈ ω ->
  int_ctor m1 n1 = int_ctor m2 n2 -> m1 +ₙ n2 = n1 +ₙ m2.
Proof.
  intros m1 n1 m2 n2 P1 P2 P3.
  pose (cp_intro _ _ _ _ P1 P2) as P4.
  pose (equiv_class_eq_elim _ _ _ _ int_ctor_rel_is_equiv_rel P4 P3) as P5.
  destruct (subset_elim _ _ _ P5) as [_ [a [b [c [d [P6 P7]]]]]].
  rewrite (opair_equal_elim_fst _ _ _ _ (opair_equal_elim_fst _ _ _ _ P6)).
  rewrite (opair_equal_elim_fst _ _ _ _ (opair_equal_elim_snd _ _ _ _ P6)).
  rewrite (opair_equal_elim_snd _ _ _ _ (opair_equal_elim_fst _ _ _ _ P6)).
  rewrite (opair_equal_elim_snd _ _ _ _ (opair_equal_elim_snd _ _ _ _ P6)).
  apply P7.
Qed.

Lemma int_elim_snd: forall m n, int_ctor m n ∈ ℤ -> n ∈ ω.
Proof.
  intros m n P1.
  destruct (int_elim _ P1) as [m2 [n2 [P2 [P3 P4]]]].
  symmetry in P4.
  pose (equiv_class_eq_elim _ _ _ _ 
    int_ctor_rel_is_equiv_rel (cp_intro _ _ _ _ P2 P3) P4) as P5.
  pose (equiv_rel_elim_2 _ _ _ _ int_ctor_rel_is_equiv_rel P5) as P6.
  destruct (cp_elim_2 _ _ _ _ P6) as [_ P7].
  apply P7.
Qed.

Definition int_add :=
  subset_ctor (fun x => exists m n p q z,
    x = ⟨⟨int_ctor m n , int_ctor p q⟩, z⟩ /\
    z = int_ctor (m +ₙ p) (n +ₙ q)) (cp (cp ℤ ℤ) ℤ).

Lemma support_add: forall a b c d, a ∈ ω -> b ∈ ω -> c ∈ ω -> d ∈ ω ->
  (a +ₙ b) +ₙ (c +ₙ d) = (d +ₙ b) +ₙ (c +ₙ a).
Proof.
  intros a b c d Pa Pb Pc Pd.
  rewrite (add_associative _ _ _ (add_is_nat _ _ Pa Pb) Pc Pd).
  rewrite (add_commutative _ _ (add_is_nat _ _ Pa Pb) Pc).
  rewrite (add_associative _ _ _ Pc Pa Pb).
  rewrite <- (add_associative _ _ _ (add_is_nat _ _ Pc Pa) Pb Pd).
  rewrite (add_commutative _ _ (add_is_nat _ _ Pc Pa) (add_is_nat _ _ Pb Pd)).
  rewrite (add_commutative _ _ Pb Pd). 
  reflexivity.
Qed.
  
Lemma int_add_is_function: function int_add.
Proof.
  split.
  + apply cp_subset_rel.
  + intros a b1 b2 P1 P2.
    destruct (subset_elim _ _ _ P1) as [Q1 [qm [qn [qp [qq [ql [Q2 Q3]]]]]]].
    destruct (cp_elim_2 _ _ _ _ Q1) as [Q4 Q5].
    destruct (cp_elim _ _ _ Q4) as [qa [qb [Q6 [Q7 Q8]]]].
    rewrite (opair_equal_elim_snd _ _ _ _ Q2).
    rewrite Q3.
    rewrite (opair_equal_elim_fst _ _ _ _ Q2) in Q4.
    destruct (cp_elim_2 _ _ _ _ Q4) as [Q9 Q10].
    destruct (subset_elim _ _ _ P2) as [R1 [rm [rn [rp [rq [rl [R2 R3]]]]]]].
    destruct (cp_elim_2 _ _ _ _ R1) as [R4 R5].
    destruct (cp_elim _ _ _ R4) as [ra [rb [R6 [R7 R8]]]].
    rewrite (opair_equal_elim_snd _ _ _ _ R2).
    rewrite R3.
    rewrite (opair_equal_elim_fst _ _ _ _ R2) in R4.
    destruct (cp_elim_2 _ _ _ _ R4) as [R9 R10].
    apply equiv_class_eq_intro.
    apply (equiv_class_intro_1 _ _ _ _ int_ctor_rel_is_equiv_rel).
    apply subset_intro.
    - apply cp_intro.
      * apply cp_intro.
        ++apply add_is_nat.
          --apply (int_elim_fst _ _ Q9).  
          --apply (int_elim_fst _ _ Q10).
        ++apply add_is_nat.
          --apply (int_elim_snd _ _ Q9).  
          --apply (int_elim_snd _ _ Q10).
      * apply cp_intro.
        ++apply add_is_nat.
          --apply (int_elim_fst _ _ R9).  
          --apply (int_elim_fst _ _ R10).
        ++apply add_is_nat.
          --apply (int_elim_snd _ _ R9).  
          --apply (int_elim_snd _ _ R10).
    - exists (qm +ₙ qp). exists (qn +ₙ qq). 
      exists (rm +ₙ rp). exists (rn +ₙ rq).
      split.
      * reflexivity.
      * pose (opair_equal_elim_fst _ _ _ _ Q2) as P3.
        rewrite (opair_equal_elim_fst _ _ _ _ R2) in P3.
        rewrite (support_add _ _ _ _ 
          (int_elim_fst _ _ Q9) (int_elim_fst _ _ Q10)
          (int_elim_snd _ _ R9) (int_elim_snd _ _ R10)).
        rewrite (support_add _ _ _ _ 
          (int_elim_snd _ _ Q9) (int_elim_snd _ _ Q10)
          (int_elim_fst _ _ R9) (int_elim_fst _ _ R10)).
        rewrite (int_equal_elim _ _ _ _ (int_elim_fst _ _ R9) 
          (int_elim_snd _ _ R9) (opair_equal_elim_fst _ _ _ _ P3)).
        rewrite (int_equal_elim _ _ _ _ (int_elim_fst _ _ R10) 
          (int_elim_snd _ _ R10) (opair_equal_elim_snd _ _ _ _ P3)).
        reflexivity.
Qed.

Notation "x +z y" := (int_add [ ⟨x, y⟩ ]) (at level 60, no associativity).

(* TODO: Law of int add *)
(* TODO: def two variable function *)
(* TODO: refine equiv and int *)
(* TODO: refine names, intro -> i, elim -> e, equal -> eq ...*)
(* TODO: refine elim_1 2 3 ... to some meanful name? *)




