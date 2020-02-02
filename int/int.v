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


