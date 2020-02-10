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

(* Rational Number *)
Definition rat_ctor_rel := 
  subset_ctor (fun x => 
    exists a b c d, x = ⟨⟨a, b⟩, ⟨c, d⟩⟩ /\ a ×z d = b ×z c)
    (cp (cp ℤ ℤ') (cp ℤ ℤ')).

Lemma rat_ctor_rel_refl: r_refl rat_ctor_rel (cp ℤ ℤ').
Proof.
  intros x P1.
  apply subset_intro.
  + apply cp_intro.
    - apply P1.
    - apply P1.
  + destruct (cp_elim _ _ _ P1) as [a [b [P2 [P3 P4]]]].
    exists a. exists b. exists a. exists b.
    split.
    - rewrite P4.
      reflexivity.
    - apply (int_multi_commutative _ _ P2 (in_subz _ P3)).
Qed.

Lemma rat_ctor_rel_sym: r_sym rat_ctor_rel.
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
      rewrite (int_multi_commutative _ _ Q3 (in_subz _ Q2)).
      rewrite (int_multi_commutative _ _ (in_subz _ Q4) Q1).
      symmetry.
      apply P4.
Qed.

Lemma rat_ctor_rel_trans: r_trans rat_ctor_rel.
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
      rewrite (opair_equal_elim_fst _ _ _ _ P3) in R3.
      rewrite (opair_equal_elim_snd _ _ _ _ P3) in R3.
      pose (int_equal_multi _ _ b4 Q3) as P4.
      pose (int_equal_multi _ _ a2 R3) as P5.
      rewrite (int_multi_commutative (a3 ×z b4) a2) in P5.
      rewrite (int_multi_associative a2 a3 b4) in P5. 
      rewrite <- P4 in P5.
      rewrite <- (int_multi_associative a1 a4 b4) in P5. 
      rewrite (int_multi_commutative a4 b4) in P5.
      rewrite (int_multi_associative a1 b4 a4) in P5. 
      rewrite (int_multi_commutative (a4 ×z b3) a2) in P5.
      rewrite (int_multi_commutative a4 b3) in P5.
      rewrite (int_multi_associative a2 b3 a4) in P5. 
      apply (int_multi_cancellation _ _ a4).
      all: is_int.
Qed.

Lemma rat_ctor_rel_is_equiv_rel: equiv_rel rat_ctor_rel (cp ℤ ℤ').
Proof.
  split. split.
  + apply cp_subset_rel.
  + split.
    - apply (cp_subset_dom _ _ (cp ℤ ℤ')).
      apply (subset_elim_2).
    - apply (cp_subset_ran _ (cp ℤ ℤ') _).
      apply (subset_elim_2).
  + split.
    - apply rat_ctor_rel_refl. 
    - split.
      * apply rat_ctor_rel_sym.
      * apply rat_ctor_rel_trans.
Qed.

Definition ℚ := (cp ℤ ℤ')[\ rat_ctor_rel].

Definition rat (m: set) (n: set) :=
  (cp ℤ ℤ')[rat_ctor_rel, ⟨m, n⟩].

Notation "q.0" := (rat z.0 z.1).

Notation "q.1" := (rat z.1 z.1).

Notation "q.-1" := (rat z.-1 z.1).

Lemma rat_ctor_is_rat: forall m n, m ∈ ℤ -> n ∈ ℤ' -> rat m n ∈ ℚ.
Proof.
  intros m n P1 P2.
  apply (equiv_part_intro _ _ _ rat_ctor_rel_is_equiv_rel).
  apply (cp_intro _ _ _ _ P1 P2).
Qed.

Lemma rat_elim: forall x, x ∈ ℚ -> exists m n, 
  m ∈ ℤ /\ n ∈ ℤ' /\ x = (rat m n).
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

Lemma rat_elim_fst: forall m n, rat m n ∈ ℚ -> m ∈ ℤ.
Proof.
  intros m n P1.
  destruct (rat_elim _ P1) as [m2 [n2 [P2 [P3 P4]]]].
  symmetry in P4.
  pose (equiv_class_eq_elim _ _ _ _ 
    rat_ctor_rel_is_equiv_rel (cp_intro _ _ _ _ P2 P3) P4) as P5.
  pose (equiv_rel_elim_2 _ _ _ _ rat_ctor_rel_is_equiv_rel P5) as P6.
  destruct (cp_elim_2 _ _ _ _ P6) as [P7 _].
  apply P7.
Qed.

Lemma rat_elim_snd: forall m n, rat m n ∈ ℚ -> n ∈ ℤ'.
Proof.
  intros m n P1.
  destruct (rat_elim _ P1) as [m2 [n2 [P2 [P3 P4]]]].
  symmetry in P4.
  pose (equiv_class_eq_elim _ _ _ _ 
    rat_ctor_rel_is_equiv_rel (cp_intro _ _ _ _ P2 P3) P4) as P5.
  pose (equiv_rel_elim_2 _ _ _ _ rat_ctor_rel_is_equiv_rel P5) as P6.
  destruct (cp_elim_2 _ _ _ _ P6) as [_ P7].
  apply P7.
Qed.

Lemma rat_intro: forall m n, m ∈ ℤ -> n ∈ ℤ' -> rat m n ∈ ℚ.
Proof.
  intros m n P1 P2.
  apply subset_intro.
  + apply subset_in_power.
    intros x P3.
    apply (equiv_rel_elim_2 _ _ _ _ rat_ctor_rel_is_equiv_rel 
      (equiv_class_elim_1 _ _ _ _ P3)).
  + exists (⟨m, n⟩).
    split.
    - is_int.
    - reflexivity.
Qed.

Lemma zero_is_rat: q.0 ∈ ℚ.
Proof.
  apply rat_intro.
  apply zero_is_int.
  apply int_one_in_subz.
Qed.

Lemma one_is_rat: q.1 ∈ ℚ.
Proof.
  apply rat_intro.
  apply one_is_int.
  apply int_one_in_subz.
Qed.

Lemma inverse_one_is_rat: q.-1 ∈ ℚ.
Proof.
  apply rat_intro.
  apply inverse_one_is_int.
  apply int_one_in_subz.
Qed.

Lemma rat_equal_elim: forall m1 n1 m2 n2, m1 ∈ ℤ -> n1 ∈ ℤ' ->
  rat m1 n1 = rat m2 n2 -> m1 ×z n2 = n1 ×z m2.
Proof.
  intros m1 n1 m2 n2 P1 P2 P3.
  pose (cp_intro _ _ _ _ P1 P2) as P4.
  pose (equiv_class_eq_elim _ _ _ _ rat_ctor_rel_is_equiv_rel P4 P3) as P5.
  destruct (subset_elim _ _ _ P5) as [_ [a [b [c [d [P6 P7]]]]]].
  rewrite (opair_equal_elim_fst _ _ _ _ (opair_equal_elim_fst _ _ _ _ P6)).
  rewrite (opair_equal_elim_fst _ _ _ _ (opair_equal_elim_snd _ _ _ _ P6)).
  rewrite (opair_equal_elim_snd _ _ _ _ (opair_equal_elim_fst _ _ _ _ P6)).
  rewrite (opair_equal_elim_snd _ _ _ _ (opair_equal_elim_snd _ _ _ _ P6)).
  apply P7.
Qed.

Lemma rat_equal_intro: forall m1 n1 m2 n2, m1 ∈ ℤ -> n1 ∈ ℤ' ->
  m2 ∈ ℤ -> n2 ∈ ℤ' -> m1 ×z n2 = n1 ×z m2 -> rat m1 n1 = rat m2 n2.
Proof.
  intros m1 n1 m2 n2 P1 P2 P3 P4 P5.
  apply equiv_class_eq_intro.
  apply (equiv_class_intro_1 _ _ _ _ rat_ctor_rel_is_equiv_rel).
  apply subset_intro.
  + is_int.
  + exists m1. exists n1. exists m2. exists n2.
    split.
    - reflexivity.
    - apply P5.
Qed.

Ltac is_int_q :=
  repeat match goal with
    | [ H: rat ?P _ ∈ ℚ |- ?P ∈ ℤ      ] => apply (rat_elim_fst _ _ H)
    | [ H: rat _ ?P ∈ ℚ |- ?P ∈ ℤ      ] => apply (in_subz _ (rat_elim_snd _ _ H))
    | [ H: rat _ ?P ∈ ℚ |- ?P ∈ ℤ'     ] => apply (rat_elim_snd _ _ H)
    | [                 |- ⟨_, _⟩ ∈  ℚ ] => apply (rat_intro)
    | [                 |- rat _ _ ∈ ℚ ] => apply (rat_ctor_is_rat)
    | _ => is_int
  end.
(*----------------------------------------------------------------------------*)

(* Addition *)
Definition rat_add :=
  subset_ctor (fun x => exists m n p q,
    x = ⟨⟨rat m n , rat p q⟩, 
    rat ((m ×z q) +z (n ×z p)) (n ×z q)⟩) (cp (cp ℚ ℚ) ℚ).

Notation "x +q y" := (rat_add [ ⟨x, y⟩ ]) (at level 60, no associativity).

Lemma rat_add_is_function: function rat_add.
Proof.
  split.
  + apply cp_subset_rel.
  + intros a b1 b2 P1 P2.
    destruct (subset_elim _ _ _ P1) as [Q1 [qm [qn [qp [qq Q2]]]]].
    destruct (cp_elim_2 _ _ _ _ Q1) as [Q4 Q5].
    destruct (cp_elim _ _ _ Q4) as [qa [qb [Q6 [Q7 Q8]]]].
    rewrite (opair_equal_elim_snd _ _ _ _ Q2).
    rewrite (opair_equal_elim_fst _ _ _ _ Q2) in Q4.
    destruct (cp_elim_2 _ _ _ _ Q4) as [Q9 Q10].
    destruct (subset_elim _ _ _ P2) as [R1 [rm [rn [rp [rq R2]]]]].
    destruct (cp_elim_2 _ _ _ _ R1) as [R4 R5].
    destruct (cp_elim _ _ _ R4) as [ra [rb [R6 [R7 R8]]]].
    rewrite (opair_equal_elim_snd _ _ _ _ R2).
    rewrite (opair_equal_elim_fst _ _ _ _ R2) in R4.
    destruct (cp_elim_2 _ _ _ _ R4) as [R9 R10].
    apply equiv_class_eq_intro.
    apply (equiv_class_intro_1 _ _ _ _ rat_ctor_rel_is_equiv_rel).
    apply subset_intro.
    - is_int_q.
    - exists ((qm ×z qq) +z (qn ×z qp)).
      exists (qn ×z qq).
      exists ((rm ×z rq) +z (rn ×z rp)).
      exists (rn ×z rq). 
      split.
      * reflexivity.
      * pose (opair_equal_elim_fst _ _ _ _ Q2) as P3.
        rewrite (opair_equal_elim_fst _ _ _ _ R2) in P3.
        rewrite (int_distributive_r (qm ×z qq) (qn ×z qp) (rn ×z rq)).
        rewrite (int_distributive_l (qn ×z qq) (rm ×z rq) (rn ×z rp)).
        
        rewrite (int_multi_associative (qm ×z qq) rn rq).
        rewrite <- (int_multi_associative qm qq rn).
        rewrite (int_multi_commutative qq rn).
        rewrite (int_multi_associative qm rn qq).
        rewrite <- (int_multi_associative (qm ×z rn) qq rq).
        rewrite (int_multi_commutative qm rn).

        rewrite (int_multi_associative (qn ×z qq) rm rq).
        rewrite <- (int_multi_associative qn qq rm).
        rewrite (int_multi_commutative qq rm).
        rewrite (int_multi_associative qn rm qq).
        rewrite <- (int_multi_associative (qn ×z rm) qq rq).
        rewrite (int_multi_commutative qn rm).
        rewrite (rat_equal_elim _ _ _ _ (rat_elim_fst _ _ R9) 
          (rat_elim_snd _ _ R9) (opair_equal_elim_fst _ _ _ _ P3)).
        
        rewrite <- (int_multi_associative qn qp (rn ×z rq)).
        rewrite (int_multi_associative qp rn rq).
        rewrite (int_multi_commutative qp rn).
        rewrite <- (int_multi_associative rn qp rq).
        rewrite (int_multi_associative qn rn (qp ×z rq)).
        rewrite (int_multi_commutative qp rq).

        rewrite <- (int_multi_associative qn qq (rn ×z rp)).
        rewrite (int_multi_associative qq rn rp).
        rewrite (int_multi_commutative qq rn).
        rewrite <- (int_multi_associative rn qq rp).
        rewrite (int_multi_associative qn rn (qq ×z rp)).
        rewrite (int_multi_commutative qq rp).
        rewrite (rat_equal_elim _ _ _ _ (rat_elim_fst _ _ R10) 
          (rat_elim_snd _ _ R10) (opair_equal_elim_snd _ _ _ _ P3)).
        reflexivity.
        all: is_int_q.
Qed.

Lemma rat_add_dom: dom(rat_add) = cp ℚ ℚ.
Proof.
  apply subset_asym.
  split.
  + intros x P1.
    destruct (dom_elim _ _ P1) as [y P2].
    destruct (cp_elim_2 _ _ _ _ (subset_elim_2 _ _ _ P2)) as [P3 _].
    apply P3. 
  + intros x P1.
    destruct (cp_elim _ _ _ P1) as [a [b [P2 [P3 P4]]]].
    destruct (rat_elim _ P2) as [qm [qn [Q1 [Q2 Q3]]]].
    destruct (rat_elim _ P3) as [rm [rn [R1 [R2 R3]]]].
    apply dom_intro.
    exists (rat ((qm ×z rn) +z (qn ×z rm)) (qn ×z rn)).
    apply subset_intro.
    - is_int_q. 
    - exists qm. exists qn. exists rm. exists rn.
      rewrite P4.
      rewrite Q3.
      rewrite R3.
      reflexivity.
Qed.

Lemma rat_add_ran: ran(rat_add) = ℚ.
Proof.
  apply subset_asym.
  split.
  + intros y P1.
    destruct (ran_elim _ _ P1) as [x P2].
    destruct (cp_elim_2 _ _ _ _ (subset_elim_2 _ _ _ P2)) as [_ P3].
    apply P3. 
  + intros y P1.
    destruct (rat_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
    apply ran_intro.
    exists (⟨rat qm qn, rat z.0 z.1⟩).
    apply subset_intro.
    - is_int_q.
    - exists qm. exists qn. exists z.0. exists z.1.
      rewrite Q3.
      rewrite (int_multi_zero _ (in_subz _ Q2)). 
      rewrite (int_multi_one _ Q1).
      rewrite (int_multi_one _ (in_subz _ Q2)).
      rewrite (int_add_zero _ Q1).
      reflexivity.
Qed.

Lemma rat_add_is_rat: forall a b, a ∈ ℚ -> b ∈ ℚ -> a +q b ∈ ℚ.
Proof.
  intros a b P1 P2.
  rewrite <- rat_add_ran.
  apply (fval_ran _ _ rat_add_is_function).
  rewrite rat_add_dom.
  apply cp_intro.
  + apply P1.
  + apply P2.
Qed.

Ltac is_int_q2 :=
  repeat match goal with
    | [ |- _ +q _ ∈ ℚ ] => apply rat_add_is_rat
    | _                 => is_int_q
  end.

Lemma rat_add_elim: forall m n p q, m ∈ ℤ -> n ∈ ℤ' -> p ∈ ℤ -> q ∈ ℤ' ->
  (rat m n) +q (rat p q) = (rat ((m ×z q) +z (n ×z p)) (n ×z q)).
Proof.
  intros m n p q P1 P2 P3 P4.
  symmetry.
  apply (fval_intro _ _ _ rat_add_is_function).
  apply subset_intro.
  + is_int_q2. 
  + exists m. exists n. exists p. exists q.
    reflexivity.
Qed.

Lemma rat_add_commutative: forall a b, a ∈ ℚ -> b ∈ ℚ -> a +q b = b +q a.
Proof.
  intros a b P1 P2.
  destruct (rat_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (rat_elim _ P2) as [rm [rn [R1 [R2 R3]]]].
  apply (fval_intro _ _ _ rat_add_is_function).
  apply (subset_intro).
  + is_int_q2.
  + exists rm. exists rn. exists qm. exists qn.
    rewrite Q3.
    rewrite R3.
    rewrite (rat_add_elim _ _ _ _ Q1 Q2 R1 R2).
    rewrite (int_add_commutative (qm ×z rn) (qn ×z rm)).
    rewrite (int_multi_commutative rm qn).
    rewrite (int_multi_commutative rn qm).
    rewrite (int_multi_commutative rn qn).
    reflexivity.
    all: is_int_q2.
Qed.

Lemma rat_add_associative: forall a b c, a ∈ ℚ -> b ∈ ℚ -> c ∈ ℚ -> 
  a +q (b +q c) = (a +q b) +q c.
Proof.
  intros a b c P1 P2 P3.
  destruct (rat_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (rat_elim _ P2) as [rm [rn [R1 [R2 R3]]]].
  destruct (rat_elim _ P3) as [sm [sn [S1 [S2 S3]]]].
  destruct (rat_elim _ (rat_add_is_rat _ _ P1 P2)) as [tm [tn [T1 [T2 T3]]]].
  destruct (rat_elim _ (rat_add_is_rat _ _ P2 P3)) as [um [un [U1 [U2 U3]]]].
  apply (fval_intro _ _ _ rat_add_is_function).
  apply (subset_intro).
  + is_int_q2.
  + exists tm. exists tn. exists sm. exists sn.
    apply (opair_equal_intro).
    - rewrite T3.
      rewrite S3.
      reflexivity.
    - rewrite <- (rat_add_elim _ _ _ _ T1 T2 S1 S2).
      rewrite <- T3.
      rewrite Q3.
      rewrite R3.
      rewrite S3.
      rewrite (rat_add_elim _ _ _ _ R1 R2 S1 S2).
      rewrite (rat_add_elim _ _ _ _ Q1 Q2 R1 R2).
      rewrite (rat_add_elim qm qn _ _).
      rewrite (rat_add_elim _ _ sm sn).
      rewrite (int_distributive_l qn (rm ×z sn) (rn ×z sm)).
      rewrite (int_distributive_r (qm ×z rn) (qn ×z rm) sn).
      rewrite (int_multi_associative qn rn sn).
      rewrite (int_multi_associative qn rn sm).
      rewrite (int_multi_associative qn rm sn).
      rewrite (int_multi_associative qm rn sn).
      rewrite (int_add_associative
        ((qm ×z rn) ×z sn) ((qn ×z rm) ×z sn) ((qn ×z rn) ×z sm)).
      reflexivity.
      all: is_int.
Qed.

Lemma rat_add_zero: forall a, a ∈ ℚ -> a +q q.0 = a.
Proof.
  intros a P1.
  destruct (rat_elim _ P1) as [m [n [P2 [P3 P4]]]].
  rewrite P4.
  rewrite (rat_add_elim _ _ _ _ P2 P3 zero_is_int int_one_in_subz).
  rewrite (int_multi_one _ P2).
  rewrite (int_multi_one _ (in_subz _ P3)).
  rewrite (int_multi_zero _ (in_subz _ P3)).
  rewrite (int_add_zero _ P2).
  reflexivity.
Qed.
(*----------------------------------------------------------------------------*)

(* Multiple *)
Definition rat_multi :=
  subset_ctor (fun x => exists m n p q,
    x = ⟨⟨rat m n , rat p q⟩, rat (m ×z p) (n ×z q)⟩) 
    (cp (cp ℚ ℚ) ℚ).

Notation "x ×q y" := (rat_multi [ ⟨x, y⟩ ]) (at level 60, no associativity).

Lemma rat_multi_is_function: function rat_multi.
Proof.
  split.
  + apply cp_subset_rel.
  + intros a b1 b2 P1 P2.
    destruct (subset_elim _ _ _ P1) as [Q1 [qm [qn [qp [qq Q2]]]]].
    destruct (cp_elim_2 _ _ _ _ Q1) as [Q4 Q5].
    destruct (cp_elim _ _ _ Q4) as [qa [qb [Q6 [Q7 Q8]]]].
    rewrite (opair_equal_elim_snd _ _ _ _ Q2).
    rewrite (opair_equal_elim_fst _ _ _ _ Q2) in Q4.
    destruct (cp_elim_2 _ _ _ _ Q4) as [Q9 Q10].
    destruct (subset_elim _ _ _ P2) as [R1 [rm [rn [rp [rq R2]]]]].
    destruct (cp_elim_2 _ _ _ _ R1) as [R4 R5].
    destruct (cp_elim _ _ _ R4) as [ra [rb [R6 [R7 R8]]]].
    rewrite (opair_equal_elim_snd _ _ _ _ R2).
    rewrite (opair_equal_elim_fst _ _ _ _ R2) in R4.
    destruct (cp_elim_2 _ _ _ _ R4) as [R9 R10].
    apply equiv_class_eq_intro.
    apply (equiv_class_intro_1 _ _ _ _ rat_ctor_rel_is_equiv_rel).
    apply subset_intro.
    - is_int_q2.
    - exists (qm ×z qp). 
      exists (qn ×z qq). 
      exists (rm ×z rp).
      exists (rn ×z rq).
      split.
      * reflexivity.
      * rewrite (int_multi_associative (qm ×z qp) rn rq).
        rewrite <- (int_multi_associative qm qp rn).
        rewrite (int_multi_commutative qp rn).
        rewrite (int_multi_associative qm rn qp).
        rewrite <- (int_multi_associative (qm ×z rn) qp rq).
        rewrite (int_multi_commutative qm rn).
        rewrite (int_multi_commutative qp rq).

        rewrite (int_multi_associative (qn ×z qq) rm rp).
        rewrite <- (int_multi_associative qn qq rm).
        rewrite (int_multi_commutative qq rm).
        rewrite (int_multi_associative qn rm qq).
        rewrite <- (int_multi_associative (qn ×z rm) qq rp).
        rewrite (int_multi_commutative qn rm).
        rewrite (int_multi_commutative qq rp).

        pose (opair_equal_elim_fst _ _ _ _ Q2) as P3.
        rewrite (opair_equal_elim_fst _ _ _ _ R2) in P3. 
        rewrite (rat_equal_elim _ _ _ _ 
          (rat_elim_fst _ _ R9) (rat_elim_snd _ _ R9) 
          (opair_equal_elim_fst _ _ _ _ P3)).
        rewrite (rat_equal_elim _ _ _ _ 
          (rat_elim_fst _ _ R10) (rat_elim_snd _ _ R10) 
          (opair_equal_elim_snd _ _ _ _ P3)).
        reflexivity.
        all: is_int_q2.
Qed.

Lemma rat_multi_dom: dom(rat_multi) = cp ℚ ℚ.
Proof.
  apply (subset_asym).
  split.
  + intros x P1.
    destruct (dom_elim _ _ P1) as [y P2].
    destruct (subset_elim _ _ _ P2) as [P3 _].
    destruct (cp_elim_2 _ _ _ _ P3) as [P4 _].
    apply P4.
  + intros x P1.
    destruct (cp_elim _ _ _ P1) as [a [b [P2 [P3 P4]]]].
    destruct (rat_elim _ P2) as [qm [qn [Q1 [Q2 Q3]]]].
    destruct (rat_elim _ P3) as [rm [rn [R1 [R2 R3]]]].
    apply dom_intro.
    exists (rat (qm ×z rm) (qn ×z rn)).
    apply subset_intro.
    - is_int_q2.
    - exists qm. exists qn. exists rm. exists rn.
      rewrite P4.
      rewrite Q3.
      rewrite R3.
      reflexivity. 
Qed.

Lemma rat_multi_ran: ran(rat_multi) = ℚ.
Proof.
  apply (subset_asym).
  split.
  + intros y P1.
    destruct (ran_elim _ _ P1) as [x P2].
    destruct (subset_elim _ _ _ P2) as [P3 _].
    destruct (cp_elim_2 _ _ _ _ P3) as [_ P4].
    apply P4.
  + intros x P1.
    destruct (rat_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
    apply ran_intro.
    exists (⟨rat qm qn, rat z.1 z.1⟩).
    apply subset_intro.
    - is_int_q2.
    - exists qm. exists qn. exists z.1. exists z.1.
      rewrite Q3.
      rewrite (int_multi_one _ Q1).
      rewrite (int_multi_one _ (in_subz _ Q2)).
      reflexivity. 
Qed.

Lemma rat_multi_is_rat: forall a b, a ∈ ℚ -> b ∈ ℚ -> a ×q b ∈ ℚ.
Proof.
  intros a b P1 P2.
  rewrite <- rat_multi_ran.
  apply (fval_ran _ _ rat_multi_is_function).
  rewrite rat_multi_dom.
  apply cp_intro.
  + apply P1.
  + apply P2.
Qed.

Ltac is_int_q3 :=
  repeat match goal with
    | [ |- _ ×q _ ∈ ℚ ] => apply rat_multi_is_rat
    | _                 => is_int_q2
  end.

Lemma rat_multi_elim: forall m n p q, m ∈ ℤ -> n ∈ ℤ' -> p ∈ ℤ -> q ∈ ℤ' ->
  (rat m n) ×q (rat p q) = (rat (m ×z p) (n ×z q)).
Proof.
  intros m n p q P1 P2 P3 P4.
  symmetry.
  apply (fval_intro _ _ _ rat_multi_is_function).
  apply subset_intro.
  + is_int_q3. 
  + exists m. exists n. exists p. exists q.
    reflexivity.
Qed.

Lemma rat_multi_commutative: forall a b, a ∈ ℚ -> b ∈ ℚ -> a ×q b = b ×q a.
Proof.
  intros a b P1 P2.
  destruct (rat_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (rat_elim _ P2) as [rm [rn [R1 [R2 R3]]]].
  apply (fval_intro _ _ _ rat_multi_is_function).
  apply (subset_intro).
  + is_int_q3.
  + exists rm. exists rn. exists qm. exists qn.
    rewrite Q3.
    rewrite R3.
    rewrite (rat_multi_elim _ _ _ _ Q1 Q2 R1 R2).
    rewrite (int_multi_commutative _ _ Q1 R1).
    rewrite (int_multi_commutative _ _ (in_subz _ Q2) (in_subz _ R2)).
    reflexivity.
    all: is_int.
Qed.

Lemma rat_multi_associative: forall a b c, a ∈ ℚ -> b ∈ ℚ -> c ∈ ℚ -> 
  a ×q (b ×q c) = (a ×q b) ×q c.
Proof.
  intros a b c P1 P2 P3.
  destruct (rat_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (rat_elim _ P2) as [rm [rn [R1 [R2 R3]]]].
  destruct (rat_elim _ P3) as [sm [sn [S1 [S2 S3]]]].
  destruct (rat_elim _ (rat_multi_is_rat _ _ P1 P2)) as [tm [tn [T1 [T2 T3]]]].
  destruct (rat_elim _ (rat_multi_is_rat _ _ P2 P3)) as [um [un [U1 [U2 U3]]]].
  apply (fval_intro _ _ _ rat_multi_is_function).
  apply (subset_intro).
  + is_int_q3.
  + exists tm. exists tn. exists sm. exists sn.
    apply (opair_equal_intro).
    - rewrite T3.
      rewrite S3.
      reflexivity.
    - rewrite <- (rat_multi_elim _ _ _ _ T1 T2 S1 S2).
      rewrite <- T3.
      rewrite Q3.
      rewrite R3.
      rewrite S3.
      rewrite (rat_multi_elim _ _ _ _ R1 R2 S1 S2).
      rewrite (rat_multi_elim _ _ _ _ Q1 Q2 R1 R2).
      rewrite (rat_multi_elim qm qn _ _).
      rewrite (rat_multi_elim _ _ sm sn).
      rewrite (int_multi_associative qm rm sm).
      rewrite (int_multi_associative qn rn sn).
      reflexivity.
      all: is_int.
Qed.

Lemma rat_multi_zero: forall a, a ∈ ℚ -> a ×q q.0 = q.0.
Proof.
  intros a P1.
  destruct (rat_elim _ P1) as [m [n [P2 [P3 P4]]]].
  rewrite P4.
  rewrite (rat_multi_elim _ _ _ _ P2 P3 zero_is_int int_one_in_subz).
  rewrite (int_multi_zero _ P2).
  rewrite (int_multi_one _ (in_subz _ P3)).
  apply (rat_equal_intro).
  all: is_int.
  rewrite (int_multi_zero _ (in_subz _ P3)).
  rewrite (int_multi_one _ zero_is_int).
  reflexivity.
Qed.

Lemma rat_multi_one: forall a, a ∈ ℚ -> a ×q q.1 = a.
Proof.
  intros a P1.
  destruct (rat_elim _ P1) as [m [n [P2 [P3 P4]]]].
  rewrite P4.
  rewrite (rat_multi_elim _ _ _ _ P2 P3 one_is_int int_one_in_subz).
  rewrite (int_multi_one _ P2).
  rewrite (int_multi_one _ (in_subz _ P3)).
  reflexivity.
Qed.

Lemma rat_distributive_l: forall m n p, m ∈ ℚ -> n ∈ ℚ -> p ∈ ℚ ->
  m ×q (n +q p) = (m ×q n) +q (m ×q p).
Proof.
  intros m n p P1 P2 P3.
  destruct (rat_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (rat_elim _ P2) as [rm [rn [R1 [R2 R3]]]].
  destruct (rat_elim _ P3) as [sm [sn [S1 [S2 S3]]]].
  rewrite Q3.
  rewrite R3.
  rewrite S3.
  rewrite (rat_add_elim _ _ _ _ R1 R2 S1 S2).
  rewrite (rat_multi_elim _ _ _ _ Q1 Q2 R1 R2).
  rewrite (rat_multi_elim _ _ _ _ Q1 Q2 S1 S2).
  rewrite (rat_multi_elim qm qn _ _).
  rewrite rat_add_elim. 
  apply (rat_equal_intro).
  all: is_int.
  rewrite <- (int_multi_associative qm rm (qn ×z sn)).
  rewrite (int_multi_associative rm qn sn).
  rewrite (int_multi_commutative rm qn).
  rewrite (int_multi_associative qm (qn ×z rm) sn).
  rewrite (int_multi_associative qm qn rm).
  rewrite <- (int_multi_associative (qm ×z qn) rm sn).
  rewrite (int_multi_associative (qn ×z rn) qm sm).
  rewrite <- (int_multi_associative qn rn qm).
  rewrite (int_multi_commutative rn qm).
  rewrite (int_multi_associative qn qm rn).
  rewrite <- (int_multi_associative (qn ×z qm) rn sm).
  rewrite (int_multi_commutative qn qm).
  rewrite <- (int_distributive_l (qm ×z qn) (rm ×z sn) (rn ×z sm)).
  rewrite <- (int_multi_associative 
    qm ((rm ×z sn) +z (rn ×z sm)) ((qn ×z rn) ×z (qn ×z sn))).
  rewrite (int_multi_commutative 
    ((rm ×z sn) +z (rn ×z sm)) ((qn ×z rn) ×z (qn ×z sn))).
  rewrite (int_multi_associative
    qm ((qn ×z rn) ×z (qn ×z sn)) ((rm ×z sn) +z (rn ×z sm))).
  rewrite (int_multi_associative
    (qn ×z (rn ×z sn)) (qm ×z qn) ((rm ×z sn) +z (rn ×z sm))).
  rewrite <- (int_multi_associative qn rn (qn ×z sn)).
  rewrite (int_multi_associative qm qn (rn ×z (qn ×z sn))).
  rewrite (int_multi_associative rn qn sn).
  rewrite (int_multi_commutative rn qn).
  rewrite <- (int_multi_associative qn rn sn).
  rewrite (int_multi_commutative (qm ×z qn) (qn ×z (rn ×z sn))).
  reflexivity.
  all: is_int.
Qed.

Lemma rat_distributive_r: forall m n p, m ∈ ℚ -> n ∈ ℚ -> p ∈ ℚ ->
  (m +q n) ×q p = (m ×q p) +q (n ×q p).
Proof.
  intros m n p P1 P2 P3.
  rewrite (rat_multi_commutative m p).
  rewrite (rat_multi_commutative n p).
  rewrite (rat_multi_commutative (m +q n) p).
  apply rat_distributive_l.
  all: is_int_q2.
Qed.
(*----------------------------------------------------------------------------*)

(* Skip add and multi inverse *)
(*----------------------------------------------------------------------------*)

(* Order *)
Definition rat_less_rel :=
  subset_ctor (fun x => exists m n p q, m ∈ ℤ /\ n ∈ ℤ' /\ p ∈ ℤ /\ q ∈ ℤ' /\
    x = ⟨rat m n , rat p q⟩ /\ ((m ×z q) <z (n ×z p))) (cp ℚ ℚ).

Notation "m <q n" := (⟨m, n⟩ ∈ rat_less_rel) (at level 65, no associativity).

Lemma rat_less_elim_1: forall x y, x ∈ ℚ -> y ∈ ℚ -> x <q y ->
  exists m n p q, m ∈ ℤ /\ n ∈ ℤ' /\ p ∈ ℤ /\ q ∈ ℤ' /\
    x = rat m n /\ y = rat p q /\ (m ×z q) <z (n ×z p).
Proof.
  intros x y P1 P2 P3.
  destruct (subset_elim _ _ _ P3) as [P4 [m [n [p [q [Q1 [Q2 [Q3 [Q4 [P5 P6]]]]]]]]]].
  exists m. exists n. exists p. exists q.
  repeat split.
  all: is_int.
  + apply (opair_equal_elim_fst _ _ _ _ P5).
  + apply (opair_equal_elim_snd _ _ _ _ P5).
Qed.

Lemma rat_less_elim_2: forall m n p q, m ∈ ℤ -> n ∈ ℤ' -> p ∈ ℤ -> q ∈ ℤ' -> 
  rat m n <q rat p q -> (m ×z q) <z (n ×z p).
Proof.
  intros m n p q P1 P2 P3 P4 P5.
  destruct (rat_less_elim_1 _ _ (rat_ctor_is_rat _ _ P1 P2)
    (rat_ctor_is_rat _ _ P3 P4) P5) 
    as [m2 [n2 [p2 [q2 [R1 [R2 [R3 [R4 [P6 [P7 P8]]]]]]]]]].
  pose (rat_equal_elim _ _ _ _ P1 P2 P6) as Q1.
  pose (rat_equal_elim _ _ _ _ P3 P4 P7) as Q2.
  assert (((m2 ×z q2) ×z n ×z q) <z (((n2 ×z p2) ×z n) ×z q)) as P9.
  { apply (int_less_multi_equal ((m2 ×z q2) ×z n) ((n2 ×z p2) ×z n) q).
    all: is_int.
    apply (in_subz_positive _ P4).
    apply (int_less_multi_equal (m2 ×z q2) (n2 ×z p2) n).
    all: is_int. 
    apply (in_subz_positive _ P2). }
  rewrite (int_multi_cyc m2 q2 n) in P9.
  rewrite (int_multi_commutative m2 n) in P9.
  rewrite <- Q1 in P9.
  rewrite (int_multi_cyc (m ×z n2) q2 q) in P9.
  rewrite (int_multi_cyc m n2 q) in P9.
  rewrite <- (int_multi_associative (m ×z q) n2 q2) in P9.
  rewrite (int_multi_cyc n2 p2 n) in P9.
  rewrite <- (int_multi_associative (n2 ×z n) p2 q) in P9.
  rewrite (int_multi_commutative p2 q) in P9.
  rewrite <- Q2 in P9.
  rewrite (int_multi_associative (n2 ×z n) p q2) in P9.
  rewrite (int_multi_commutative n2 n) in P9.
  rewrite (int_multi_cyc n n2 p) in P9.
  rewrite <- (int_multi_associative (n ×z p) n2 q2) in P9.
  apply (int_less_multi_cancellation _ _ (n2 ×z q2)).
  all: is_int.
Qed.

Lemma rat_less_intro: forall m n p q, m ∈ ℤ -> n ∈ ℤ' -> p ∈ ℤ -> q ∈ ℤ' -> 
  (m ×z q) <z (n ×z p) -> rat m n <q rat p q .
Proof.
  intros m n p q P1 P2 P3 P4 P5.
  apply (subset_intro).
  + is_int_q3.
  + exists m. exists n. exists p. exists q.
    repeat split.
    all: is_nat.
Qed.

Lemma rat_less_trans: forall m n l, m ∈ ℚ -> n ∈ ℚ -> l ∈ ℚ ->
 m <q n -> n <q l -> m <q l.
Proof.
  intros m n l P1 P2 P3 P4 P5.
  destruct (rat_less_elim_1 _ _ P1 P2 P4) as 
    [q1 [q2 [r1 [r2 [Q1 [Q2 [R1 [R2 [Q3 [R3 P6]]]]]]]]]].
  destruct (rat_less_elim_1 _ _ P2 P3 P5) as 
    [s1 [s2 [t1 [t2 [S1 [S2 [T1 [T2 [S3 [T3 P7]]]]]]]]]].
  rewrite R3 in S3.
  pose (rat_equal_elim _ _ _ _ R1 R2 S3) as P8.
  rewrite Q3.
  rewrite T3.
  pose (int_less_multi_equal _ _ _ 
    (int_multi_is_int _ _ Q1 (in_subz _ R2)) 
    (int_multi_is_int _ _ (in_subz _ Q2) R1) 
    (int_multi_is_int _ _ (in_subz _ S2) (in_subz _ T2)) 
    (in_subz_positive _ (int_multi_subz _ _ S2 T2)) P6) as P9. 
  rewrite (int_multi_associative (q2 ×z r1) s2 t2) in P9.
  rewrite <- (int_multi_associative q2 r1 s2) in P9.
  rewrite (int_multi_commutative q2 (r1 ×z s2)) in P9.
  rewrite <- (int_multi_associative (r1 ×z s2) q2 t2) in P9.
  rewrite (int_multi_commutative s2 t2) in P9.
  rewrite (int_multi_associative (q1 ×z r2) t2 s2) in P9.
  rewrite (int_multi_cyc q1 r2 t2) in P9.
  rewrite <- (int_multi_associative (q1 ×z t2) r2 s2) in P9.
  
  pose (int_less_multi_equal _ _ _ 
    (int_multi_is_int _ _ S1 (in_subz _ T2)) 
    (int_multi_is_int _ _ (in_subz _ S2) T1) 
    (int_multi_is_int _ _ (in_subz _ R2) (in_subz _ Q2))
    (in_subz_positive _ (int_multi_subz _ _ R2 Q2)) P7) as P10. 
  rewrite (int_multi_associative (s1 ×z t2) r2 q2) in P10.
  rewrite (int_multi_cyc s1 t2 r2) in P10.
  rewrite <- (int_multi_associative (s1 ×z r2) t2 q2) in P10.
  rewrite (int_multi_commutative s1 r2) in P10.
  rewrite (int_multi_commutative t2 q2) in P10.
  rewrite (int_multi_commutative r2 q2) in P10.
  rewrite (int_multi_associative (s2 ×z t1) q2 r2) in P10.
  rewrite <- (int_multi_associative s2 t1 q2) in P10.
  rewrite (int_multi_commutative s2 (t1 ×z q2)) in P10.
  rewrite <- (int_multi_associative (t1 ×z q2) s2 r2) in P10.
  rewrite (int_multi_commutative t1 q2) in P10.
  rewrite (int_multi_commutative s2 r2) in P10.
  rewrite <- P8 in P10.
  apply rat_less_intro.
  all: is_int.
  apply (int_less_multi_cancellation _ _ (r2 ×z s2)).
  all: is_int.
  apply (int_less_trans _ ((r1 ×z s2) ×z (q2 ×z t2)) _). 
  all: is_int.
Qed.

Lemma rat_trichotomy: forall m n, m ∈ ℚ -> n ∈ ℚ ->
  ((m <q n) /\ ~(m = n) /\ ~(n <q m)) \/
  (~(m <q n) /\ (m = n) /\ ~(n <q m)) \/
  (~(m <q n) /\ ~(m = n) /\ (n <q m)).
Proof.
  intros m n P1 P2.
  destruct (rat_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (rat_elim _ P2) as [rm [rn [R1 [R2 R3]]]]. 
  rewrite Q3.
  rewrite R3.
  destruct (int_trichotomy (qm ×z rn) (qn ×z rm)
    (int_multi_is_int _ _ Q1 (in_subz _ R2)) 
    (int_multi_is_int _ _ (in_subz _ Q2) R1)) 
      as [[P3 [P4 P5]] | [[P3 [P4 P5]] | [P3 [P4 P5]]]].
  + left.
    repeat split.
    - apply rat_less_intro.
      all: is_int.
    - intros P6.
      pose (rat_equal_elim _ _ _ _ Q1 Q2 P6) as P7.
      contradiction.
    - intros P6.
      pose (rat_less_elim_2 _ _ _ _ R1 R2 Q1 Q2 P6) as P7.
      rewrite (int_multi_commutative _ _ (in_subz _ Q2) R1) in P5.
      rewrite (int_multi_commutative _ _ Q1 (in_subz _ R2)) in P5.
      contradiction.
  + right. left.
    repeat split.
    - intros P6.
      pose (rat_less_elim_2 _ _ _ _ Q1 Q2 R1 R2 P6) as P7.
      contradiction.
    - apply (rat_equal_intro _ _ _ _ Q1 Q2 R1 R2 P4). 
    - intros P6.
      pose (rat_less_elim_2 _ _ _ _ R1 R2 Q1 Q2 P6) as P7.
      rewrite (int_multi_commutative _ _ (in_subz _ Q2) R1) in P5.
      rewrite (int_multi_commutative _ _ Q1 (in_subz _ R2)) in P5.
      contradiction.
  + right. right.
    repeat split.
    - intros P6.
      pose (rat_less_elim_2 _ _ _ _ Q1 Q2 R1 R2 P6) as P7.
      contradiction.
    - intros P6.
      pose (rat_equal_elim _ _ _ _ Q1 Q2 P6) as P7.
      contradiction.
    - rewrite (int_multi_commutative _ _ (in_subz _ Q2) R1) in P5.
      rewrite (int_multi_commutative _ _ Q1 (in_subz _ R2)) in P5.
      apply rat_less_intro.
      all: is_int.
Qed.

Lemma rat_not_less_self: forall m, m ∈ ℚ -> ~(m <q m).
Proof.
  intros m P1 P2.
  destruct (rat_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  rewrite Q3 in P2.
  pose (rat_less_elim_2 _ _ _ _ Q1 Q2 Q1 Q2 P2) as P3.
  rewrite (int_multi_commutative _ _ Q1 (in_subz _ Q2)) in P3.
  apply (int_not_less_self _ (int_multi_is_int _ _ (in_subz _ Q2) Q1) P3).
Qed.

Lemma rat_less_add_equal: forall m n p, m ∈ ℚ -> n ∈ ℚ -> p ∈ ℚ ->
  m <q n -> m +q p <q n +q p.
Proof.
  intros m n p P1 P2 P3 P4.
  destruct (rat_elim _ P1) as [qm [qn [Q1 [Q2 Q3]]]].
  destruct (rat_elim _ P2) as [rm [rn [R1 [R2 R3]]]]. 
  destruct (rat_elim _ P3) as [sm [sn [S1 [S2 S3]]]]. 
  rewrite Q3 in P4.
  rewrite R3 in P4.
  pose (rat_less_elim_2 _ _ _ _ Q1 Q2 R1 R2 P4) as P5.
  rewrite Q3.
  rewrite R3.
  rewrite S3.
  rewrite (rat_add_elim qm qn sm sn).
  rewrite (rat_add_elim rm rn sm sn).
  apply rat_less_intro.
  all: is_int.
  rewrite (int_distributive_r (qm ×z sn) (qn ×z sm) (rn ×z sn)). 
  rewrite (int_distributive_l (qn ×z sn) (rm ×z sn) (rn ×z sm)). 
  rewrite (int_multi_associative (qm ×z sn) rn sn).
  rewrite (int_multi_cyc qm sn rn).
  rewrite <- (int_multi_associative (qm ×z rn) sn sn).
  rewrite (int_multi_associative (qn ×z sn) rm sn).
  rewrite (int_multi_cyc qn sn rm).
  rewrite <- (int_multi_associative (qn ×z rm) sn sn).
  rewrite (int_multi_associative (qn ×z sm) rn sn).
  rewrite (int_multi_cyc qn sm rn).
  rewrite <- (int_multi_associative (qn ×z rn) sm sn).
  rewrite (int_multi_associative (qn ×z sn) rn sm).
  rewrite (int_multi_cyc qn sn rn).
  rewrite <- (int_multi_associative (qn ×z rn) sn sm).
  rewrite (int_multi_commutative sm sn).
  assert ((qm ×z rn) ×z (sn ×z sn) <z (qn ×z rm) ×z (sn ×z sn)) as P6.
  { apply (int_less_multi_equal _ _ (sn ×z sn)).
    all: is_int.
    apply in_subz_positive.
    apply (int_multi_subz _ _ S2 S2). }
  apply (int_less_add_equal _ _ ((qn ×z rn) ×z (sn ×z sm))).
  all: is_int.
Qed.

Lemma rat_less_add: forall m n p q, m ∈ ℚ -> n ∈ ℚ -> p ∈ ℚ -> q ∈ ℚ ->
  m <q n -> p <q q -> m +q p <q n +q q.
Proof.
  intros m n p q P1 P2 P3 P4 P5 P6.
  pose(rat_less_add_equal _ _ _ P1 P2 P3 P5) as P7. 
  pose(rat_less_add_equal _ _ _ P3 P4 P2 P6) as P8. 
  rewrite (rat_add_commutative _ _ P3 P2) in P8.
  rewrite (rat_add_commutative _ _ P4 P2) in P8.
  apply (rat_less_trans _ _ _ (rat_add_is_rat _ _ P1 P3) 
    (rat_add_is_rat _ _ P2 P3) (rat_add_is_rat _ _ P2 P4) P7 P8).
Qed.
(*----------------------------------------------------------------------------*)

(* Inverse *)
Lemma rat_add_inverse_exist: forall a, exists b, a ∈ ℚ -> b ∈ ℚ /\ a +q b = q.0.
Proof.
  intros a.
  destruct (LEM (a ∈ ℚ)) as [P1 | P1].
  + destruct (rat_elim _ P1) as [m [n [P2 [P3 P4]]]].
    exists (rat (-z m) n).
    intros P5.
    split.
    - is_int_q3. 
    - rewrite P4.
      rewrite (rat_add_elim m n (-z m) n). 
      apply (equiv_class_eq_intro).
      apply (equiv_class_intro_1 _ _ _ _ rat_ctor_rel_is_equiv_rel).
      apply (subset_intro).
      all: is_int_q2.
      exists ((m ×z n) +z (n ×z (-z m))).
      exists (n ×z n).
      exists z.0. exists z.1.
      split.
      * reflexivity.
      * rewrite (int_multi_zero (n ×z n)). 
        rewrite (int_multi_one ((m ×z n) +z (n ×z (-z m)))).
        rewrite (int_multi_commutative n (-z m)).
        rewrite <- (int_add_inverse_multi_distributive_l m n).
        rewrite (int_add_inverse_intro_2 (m ×z n)).
        reflexivity.
        all: is_int.
  + exists ∅.
    intros P2.
    contradiction.
Qed.

Definition rat_inverse (a:set) :=
  extract_set (rat_add_inverse_exist a).

Notation "-q a" := (rat_inverse a) (at level 60).

Notation "a -q b"  := (a +q (rat_inverse b)) (at level 60).

Lemma rat_add_inverse_is_rat: forall a, a ∈ ℚ -> -q a ∈ ℚ.
Proof.
  intros a P1.
  destruct (extract_set_property (rat_add_inverse_exist a) P1) as [P2 _].
  apply P2.
Qed.

Ltac is_int_q4 :=
  repeat match goal with
    | [ |- -q _ ∈ ℚ ] => apply rat_add_inverse_is_rat
    | _               => is_int_q4
  end.

Lemma rat_add_inverse_elim: forall a, a ∈ ℚ -> a +q (-q a) = q.0.
Proof.
  intros a P1.
  destruct (extract_set_property (rat_add_inverse_exist a) P1) as [_ P2].
  apply P2.
Qed.

Lemma rat_add_inverse_unique: forall a b, a ∈ ℚ -> b ∈ ℚ -> a +q b = q.0 -> 
  b = -q a.
Proof.
  intros a b P1 P2 P4.
  pose (rat_add_inverse_is_rat _ P1) as P3.
  pose (rat_add_inverse_elim _ P1) as P5.
  pose (rat_add_zero _ P2) as P6.
  rewrite <- P5 in P6.
  rewrite (rat_add_associative _ _ _ P2 P1 P3) in P6.
  rewrite (rat_add_commutative _ _ P2 P1) in P6.
  rewrite P4 in P6.
  rewrite (rat_add_commutative _ _ zero_is_rat P3) in P6.
  rewrite (rat_add_zero _ P3) in P6.
  symmetry.
  apply P6.
Qed.

Lemma inverse_one_is_inverse_one: q.-1 = -q q.1.
Proof.
  apply (rat_add_inverse_unique _ _ one_is_rat inverse_one_is_rat).
  rewrite rat_add_elim.
  rewrite (int_multi_one z.1).
  rewrite (int_multi_commutative z.1 z.-1).
  rewrite (int_multi_one z.-1).
  rewrite (inverse_one_is_inverse_one).
  rewrite (int_add_inverse_intro_2 z.1).
  all: is_int.
Qed.

Lemma rat_less_add_positive: forall m n l, m ∈ ℚ -> n ∈ ℚ -> l ∈ ℚ -> q.0 <q l
  -> m <q n -> m <q n +q l.
Proof.
  intros m n l P1 P2 P3 P4 P5.
  pose (rat_less_add _ _ _ _ P1 P2 zero_is_rat P3 P5 P4) as P6.
  rewrite (rat_add_zero _ P1) in P6.
  apply P6.
Qed.

Lemma rat_less_minus_positive: forall m n l, m ∈ ℚ -> n ∈ ℚ -> l ∈ ℚ -> q.0 <q l
  -> m <q n -> m -q l <q n.
Proof.
  intros m n l P1 P2 P3 P4 P5.
  pose (rat_less_add_positive _ _ _ P1 P2 P3 P4 P5) as P6.
  pose (rat_less_add_equal _ _ _ P1 (rat_add_is_rat _ _ P2 P3)
    (rat_add_inverse_is_rat _ P3) P6) as P7.
  rewrite <- (rat_add_associative _ _ _ P2 P3 (rat_add_inverse_is_rat _ P3)) in P7.
  rewrite (rat_add_inverse_elim _ P3) in P7.
  rewrite (rat_add_zero _ P2) in P7.
  apply P7.
Qed.

Lemma rat_less_possitive: forall m n, m ∈ ℚ -> n ∈ ℚ -> m <q n -> q.0 <q n -q m.
Proof.
  intros m n P1 P2 P3.
  pose (rat_less_add_equal _ _ _ P1 P2 (rat_add_inverse_is_rat _ P1) P3) as P4.
  rewrite (rat_add_inverse_elim _ P1) in P4.
  apply P4.
Qed.
