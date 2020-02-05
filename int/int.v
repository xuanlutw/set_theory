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

Notation "z.0" := (int_ctor n.0 n.0).

Lemma int_ctor_is_int: forall m n, m ∈ ω -> n ∈ ω -> int_ctor m n ∈ ℤ.
Proof.
  intros m n P1 P2.
  apply (equiv_part_intro _ _ _ int_ctor_rel_is_equiv_rel).
  apply (cp_intro _ _ _ _ P1 P2).
Qed.

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

Ltac is_nat_z :=
  repeat match goal with
    | [ H: int_ctor ?P _ ∈ ℤ |- ?P ∈ ω ] => apply (int_elim_fst _ _ H)
    | [ H: int_ctor _ ?P ∈ ℤ |- ?P ∈ ω ] => apply (int_elim_snd _ _ H)
    | _ => is_nat
  end.

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
    - is_nat_z.
    - exists (qm +ₙ qp). exists (qn +ₙ qq). 
      exists (rm +ₙ rp). exists (rn +ₙ rq).
      split.
      * reflexivity.
      * pose (opair_equal_elim_fst _ _ _ _ Q2) as P3.
        rewrite (opair_equal_elim_fst _ _ _ _ R2) in P3.
        apply (add_cancellation_2 _ _ _ _ 
          (int_equal_elim _ _ _ _ (int_elim_fst _ _ R9) 
          (int_elim_snd _ _ R9) (opair_equal_elim_fst _ _ _ _ P3))).
        apply (add_cancellation_2 _ _ _ _ 
          (int_equal_elim _ _ _ _ (int_elim_fst _ _ R10) 
          (int_elim_snd _ _ R10) (opair_equal_elim_snd _ _ _ _ P3))).
        nat_normal_form.
        nat_red.
        all: is_nat_z.
Qed.

Notation "x +z y" := (int_add [ ⟨x, y⟩ ]) (at level 60, no associativity).

Lemma int_add_dom: dom(int_add) = cp ℤ ℤ.
Proof.
  apply subset_asym.
  split.
  + intros x P1.
    destruct (dom_elim _ _ P1) as [y P2].
    destruct (cp_elim_2 _ _ _ _ (subset_elim_2 _ _ _ P2)) as [P3 _].
    apply P3. 
  + intros x P1.
    destruct (cp_elim _ _ _ P1) as [a [b [P2 [P3 P4]]]].
    destruct (int_elim _ P2) as [qm [qn [Q1 [Q2 Q3]]]].
    destruct (int_elim _ P3) as [rm [rn [R1 [R2 R3]]]].
    apply dom_intro.
    exists (int_ctor (qm +ₙ rm) (qn +ₙ rn)).
    apply subset_intro.
    - apply cp_intro.
      * apply P1.
      * apply (int_ctor_is_int _ _ (add_is_nat _ _ Q1 R1) (add_is_nat _ _ Q2 R2)).
    - exists qm.
      exists qn.
      exists rm.
      exists rn.
      exists (int_ctor (qm +ₙ rm) (qn +ₙ rn)).
      split.
      * rewrite P4.
        rewrite Q3.
        rewrite R3.
        reflexivity.
      * reflexivity.
Qed.

Lemma int_add_ran: ran(int_add) = ℤ.
Proof.
  apply subset_asym.
  split.
  + intros y P1.
    destruct (ran_elim _ _ P1) as [x P2].
    destruct (cp_elim_2 _ _ _ _ (subset_elim_2 _ _ _ P2)) as [_ P3].
    apply P3. 
  + intros y P1.
    destruct (int_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
    apply ran_intro.
    exists (⟨int_ctor qm qn, int_ctor n.0 n.0⟩).
    apply subset_intro.
    - apply cp_intro.
      * apply cp_intro.
        ++apply (int_ctor_is_int _ _ Q1 Q2).
        ++apply (int_ctor_is_int _ _ empty_is_nat empty_is_nat).
      * rewrite Q3. 
        apply (int_ctor_is_int _ _ Q1 Q2).
    - exists qm.
      exists qn.
      exists n.0.
      exists n.0.
      exists (int_ctor qm qn).
      split.
      * rewrite Q3.
        reflexivity.
      * rewrite (add_zero _ Q1). 
        rewrite (add_zero _ Q2). 
        reflexivity.
Qed.

Lemma int_add_is_int: forall a b, a ∈ ℤ -> b ∈ ℤ -> a +z b ∈ ℤ.
Proof.
  intros a b P1 P2.
  rewrite <- int_add_ran.
  apply (fval_ran _ _ int_add_is_function).
  rewrite int_add_dom.
  apply cp_intro.
  + apply P1.
  + apply P2.
Qed.

Lemma int_add_elim: forall m n p q, m ∈ ω -> n ∈ ω -> p ∈ ω -> q ∈ ω ->
  (int_ctor m n) +z (int_ctor p q) = (int_ctor (m +ₙ p) (n +ₙ q)).
Proof.
  intros m n p q P1 P2 P3 P4.
  symmetry.
  apply (fval_intro _ _ _ int_add_is_function).
  apply subset_intro.
  + apply cp_intro.
    - apply cp_intro.
      * apply (int_ctor_is_int _ _ P1 P2).
      * apply (int_ctor_is_int _ _ P3 P4).
    - apply int_ctor_is_int.
      * apply (add_is_nat _ _ P1 P3).
      * apply (add_is_nat _ _ P2 P4).
  + exists m.
    exists n.
    exists p.
    exists q.
    exists (int_ctor (m +ₙ p) (n +ₙ q)).
    split.
    - reflexivity.
    - reflexivity.
Qed.

Lemma int_add_commutative: forall a b, a ∈ ℤ -> b ∈ ℤ -> a +z b = b +z a.
Proof.
  intros a b P1 P2.
  destruct (int_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (int_elim _ P2) as [rm [rn [R1 [R2 R3]]]].
  apply (fval_intro _ _ _ int_add_is_function).
  apply (subset_intro).
  + apply cp_intro.
    - apply cp_intro.
      * apply P2.
      * apply P1.
    - apply (int_add_is_int _ _ P1 P2).
  + exists rm.
    exists rn.
    exists qm.
    exists qn.
    exists (a +z b).
    split.
    - rewrite Q3.
      rewrite R3.
      reflexivity.
    - rewrite Q3.
      rewrite R3.
      rewrite (int_add_elim _ _ _ _ Q1 Q2 R1 R2).
      rewrite (add_commutative _ _ Q1 R1).
      rewrite (add_commutative _ _ Q2 R2).
      reflexivity.
Qed.

Lemma int_add_associative: forall a b c, a ∈ ℤ -> b ∈ ℤ -> c ∈ ℤ -> 
  a +z (b +z c) = (a +z b) +z c.
Proof.
  intros a b c P1 P2 P3.
  destruct (int_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (int_elim _ P2) as [rm [rn [R1 [R2 R3]]]].
  destruct (int_elim _ P3) as [sm [sn [S1 [S2 S3]]]].
  destruct (int_elim _ (int_add_is_int _ _ P1 P2)) as [tm [tn [T1 [T2 T3]]]].
  destruct (int_elim _ (int_add_is_int _ _ P2 P3)) as [um [un [U1 [U2 U3]]]].
  apply (fval_intro _ _ _ int_add_is_function).
  apply (subset_intro).
  + apply cp_intro.
    - apply cp_intro.
      * apply (int_add_is_int _ _ P1 P2).
      * apply P3.
    - apply (int_add_is_int _ _ P1 (int_add_is_int _ _ P2 P3)).
  + exists tm.
    exists tn.
    exists sm.
    exists sn.
    exists (int_ctor (tm +ₙ sm) (tn +ₙ sn)).
    split.
    - apply (opair_equal_intro).
      * rewrite T3.
        rewrite S3.
        reflexivity.
      * (* WTF... *)
        symmetry. 
        apply (fval_intro _ _ _ int_add_is_function).
        apply (subset_intro).
        ++apply cp_intro.
          --apply cp_intro.
            **apply P1.
            **apply (int_add_is_int _ _ P2 P3).
          --apply int_ctor_is_int. 
            **apply (add_is_nat _ _ T1 S1).
            **apply (add_is_nat _ _ T2 S2).
        ++exists qm.
          exists qn.
          exists um.
          exists un.
          exists (int_ctor (tm +ₙ sm) (tn +ₙ sn)).
          split.
          --rewrite U3.
            rewrite Q3.
            reflexivity.
          --rewrite Q3 in T3.
            rewrite R3 in T3.
            rewrite <- (int_add_elim _ _ _ _ T1 T2 S1 S2).
            rewrite <- T3.
            rewrite (int_add_elim _ _ _ _ Q1 Q2 R1 R2).
            rewrite (int_add_elim _ _ _ _ (add_is_nat _ _ Q1 R1)
              (add_is_nat _ _ Q2 R2) S1 S2).
            rewrite R3 in U3.
            rewrite S3 in U3.
            rewrite <- (int_add_elim _ _ _ _ Q1 Q2 U1 U2).
            rewrite <- U3.
            rewrite (int_add_elim _ _ _ _ R1 R2 S1 S2).
            rewrite (int_add_elim _ _ _ _ Q1 Q2
              (add_is_nat _ _ R1 S1) (add_is_nat _ _ R2 S2)).
            f_equal.
            **symmetry.
              apply (add_associative _ _ _ Q1 R1 S1).
            **symmetry.
              apply (add_associative _ _ _ Q2 R2 S2).
    - reflexivity.
Qed.

Lemma int_add_zero: forall a, a ∈ ℤ -> a +z z.0 = a.
Proof.
  intros a P1.
  destruct (int_elim _ P1) as [m [n [P2 [P3 P4]]]].
  rewrite P4.
  rewrite (int_add_elim _ _ _ _ P2 P3 empty_is_nat empty_is_nat).
  rewrite (add_zero _ P2).
  rewrite (add_zero _ P3).
  reflexivity.
Qed.

Lemma int_add_inverse_exist: forall a, exists b, a ∈ ℤ -> b ∈ ℤ -> a +z b = z.0.
Proof.
  intros a.
  destruct (LEM (a ∈ ℤ)) as [P1 | P1].
  + destruct (int_elim _ P1) as [m [n [P2 [P3 P4]]]].
    exists (int_ctor n m).
    intros _ P5.
    rewrite P4.
    rewrite (int_add_elim _ _ _ _ P2 P3 P3 P2).
    apply (equiv_class_eq_intro).
    apply (equiv_class_intro_1 _ _ _ _ int_ctor_rel_is_equiv_rel).
    apply (subset_intro).
    - apply cp_intro.
      * apply cp_intro.
        ++apply (add_is_nat _ _ P2 P3).
        ++apply (add_is_nat _ _ P3 P2).
      * apply cp_intro.
        ++apply empty_is_nat.
        ++apply empty_is_nat.
    - exists (m +ₙ n).
      exists (n +ₙ m).
      exists n.0.
      exists n.0.
      split.
      * reflexivity.
      * rewrite (add_commutative _ _ P2 P3).
        reflexivity.
  + exists ∅.
    intros P2.
    contradiction.
Qed.

Definition int_inverse (a:set) :=
  extract_set (int_add_inverse_exist a).

Notation "z.inv a" := (int_inverse a) (at level 60).

Definition int_multi :=
  subset_ctor (fun x => exists m n p q z,
    x = ⟨⟨int_ctor m n , int_ctor p q⟩, z⟩ /\
    z = int_ctor ((m ×ₙ p) +ₙ (n ×ₙ q)) ((m ×ₙ q) +ₙ (n ×ₙ p))) (cp (cp ℤ ℤ) ℤ).

Lemma int_multi_is_function: function int_multi.
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
    - is_nat_z.
    - exists (qm ×ₙ qp +ₙ qn ×ₙ qq). 
      exists (qm ×ₙ qq +ₙ qn ×ₙ qp). 
      exists (rm ×ₙ rp +ₙ rn ×ₙ rq).
      exists (rm ×ₙ rq +ₙ rn ×ₙ rp).
      split.
      * reflexivity.
      * pose (opair_equal_elim_fst _ _ _ _ Q2) as P3.
        rewrite (opair_equal_elim_fst _ _ _ _ R2) in P3.
        pose (int_equal_elim _ _ _ _ 
          (int_elim_fst _ _ R9) (int_elim_snd _ _ R9) 
          (opair_equal_elim_fst _ _ _ _ P3)) as P4.
        apply (add_cancellation_2 _ _ _ _ (multi_equation_2 _ _ rp P4)).
        symmetry.
        apply (add_cancellation_2 _ _ _ _ (multi_equation_2 _ _ rq P4)).
        pose (int_equal_elim _ _ _ _ 
          (int_elim_fst _ _ R10) (int_elim_snd _ _ R10) 
          (opair_equal_elim_snd _ _ _ _ P3)) as P5.
        apply (add_cancellation_2 _ _ _ _ (multi_equation_2 _ _ qn P5)).
        symmetry.
        apply (add_cancellation_2 _ _ _ _ (multi_equation_2 _ _ qm P5)).
        nat_normal_form.
        rewrite (multi_commutative rq qm).
        rewrite (multi_commutative rp qn).
        rewrite (multi_commutative rq qn).
        rewrite (multi_commutative rq rm).
        rewrite (multi_commutative rp qm).
        rewrite (multi_commutative rp rn).
        rewrite (multi_commutative rn rq).
        rewrite (multi_commutative rp rm).
        nat_red.
        all: is_nat_z.
Qed.

(* TODO: Law of int add *)
(* TODO: def two variable function *)
(* TODO: refine equiv and int *)
(* TODO: refine names, intro -> i, elim -> e, equal -> eq ...*)
(* TODO: refine elim_1 2 3 ... to some meanful name? *)

(* TODO: int breakdown *)
(* TODO: nat Ltac *)




