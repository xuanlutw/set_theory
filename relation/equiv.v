Require Import axiom.logic.
Require Import axiom.axiom.
Require Import operation.basic.
Require Import relation.relation.
Require Import relation.function.

(* Equivalence Relation *)
Definition r_refl  (R: set) (A: set) := forall x, x ∈ A -> ⟨x, x⟩ ∈ R.
Definition r_sym   (R: set) := forall x y, ⟨x, y⟩ ∈ R -> ⟨y, x⟩ ∈ R.
Definition r_trans (R: set) := forall x y z, ⟨x, y⟩ ∈ R -> ⟨y, z⟩ ∈ R -> ⟨x, z⟩ ∈ R.

Definition equiv_rel (R: set) (A:set) := 
  (rover R A) /\ (r_refl R A) /\ (r_sym R) /\ (r_trans R).

Lemma sym_trans_equive: forall R, rel R -> r_sym R -> r_trans R -> 
  equiv_rel R (fld(R)).
Proof.
  intros R P1 P2 P3.
  split. 
  + split.
    - apply P1.
    - split.
      * intros x P4.
        apply (fld_intro_dom _ _ P4).
      * intros x P4.
        apply (fld_intro_ran _ _ P4).
  + split.
    - intros x P4.
      destruct (fld_elim _ _ P4) as [P5|P5].
      * destruct (dom_elim _ _ P5) as [y P6].
        apply (P3 _ _ _ P6 (P2 _ _ P6)).
      * destruct (ran_elim _ _ P5) as [y P6].
        apply (P3 _ _ _ (P2 _ _ P6) P6).
    - split.
      * apply P2.
      * apply P3.
Qed.

Lemma equiv_rel_elim_1: forall x y R A, equiv_rel R A -> ⟨x, y⟩ ∈ R -> x ∈ A.
Proof.
  intros x y R A [[_ [P1 _]] _] P2.
  apply (P1 _ (dom_intro_2 _ _ _ P2)).
Qed.

Lemma equiv_rel_elim_2: forall x y R A, equiv_rel R A -> ⟨x, y⟩ ∈ R -> y ∈ A.
Proof.
  intros x y R A [[_ [_ P1]] _] P2.
  apply (P1 _ (ran_intro_2 _ _ _ P2)).
Qed.

(* Equivalence Class *)
Definition equiv_class (x: set) (R: set) (A: set) :=
  subset_ctor (fun r => x ∈ A /\ equiv_rel R A /\ ⟨x, r⟩ ∈ R) A.

Notation "A [ R , x ]" := (equiv_class x R A) (at level 60, no associativity).

Lemma equiv_class_intro_1: forall R A x y, equiv_rel R A -> 
  ⟨x, y⟩ ∈ R -> y ∈ A[R , x].
Proof.
  intros R A x y P1 P2.
  apply (subset_intro).
  + destruct P1 as [[_ [_ P1]] _]. 
    apply (P1 _ (ran_intro_2 _ _ _ P2)). 
  + split.
    - destruct P1 as [[_ [P1 _]] _]. 
      apply (P1 _ (dom_intro_2 _ _ _ P2)). 
    - split.
      * apply P1.
      * apply P2.
Qed.

Lemma equiv_class_intro_2: forall R A x y, equiv_rel R A -> ⟨y, x⟩ ∈ R -> 
  y ∈ A[R, x].
Proof.
  intros R A x y P1 P2.
  apply equiv_class_intro_1.
  + apply P1.
  + destruct P1 as [_ [_ [P1 _]]].
    apply (P1 _ _ P2).
Qed.

Lemma equiv_class_intro_self: forall R A x, equiv_rel R A -> x ∈ A -> 
  x ∈ A[R, x].
Proof.
  intros R A x P1 P2.
  apply equiv_class_intro_1.
  + apply P1.
  + destruct P1 as [_ [P1 _]].
    apply (P1 _ P2).
Qed.

Lemma equiv_class_elim_1: forall R A x y, y ∈ A[R, x] -> ⟨x, y⟩ ∈ R.
Proof.
  intros R A x y P1.
  destruct (subset_elim _ _ _ P1) as [_ [_ [_ P2]]].
  apply P2.
Qed.

Lemma equiv_class_elim_2: forall R A x y, y ∈ A[R, x] -> ⟨y, x⟩ ∈ R.
Proof.
  intros R A x y P1.
  destruct (subset_elim _ _ _ P1) as [_ [_ [[_ [_ [P3 _]]] P2]]].
  apply (P3 _ _ P2).
Qed.

Lemma equiv_class_elim_3: forall R A x y, y ∈ A[R, x] -> y ∈ A.
Proof.
  intros R A x y P1.
  destruct (subset_elim _ _ _ P1) as [P2 _].
  apply P2.
Qed.

Lemma equiv_class_elim_4: forall R A x y, y ∈ A[R, x] -> equiv_rel R A.
Proof.
  intros R A x y P1.
  destruct (subset_elim _ _ _ P1) as [_ [_ [ P2 _]]].
  apply P2.
Qed.

Lemma equiv_class_swap: forall R A x y, y ∈ A[R, x] -> x ∈ A[R, y].
Proof.
  intros R A x y P1.
  apply equiv_class_intro_2.
  + apply (equiv_class_elim_4 _ _ _ _ P1).
  + apply (equiv_class_elim_1 _ _ _ _ P1).
Qed.

Lemma equiv_class_eq: forall R A x y, equiv_rel R A -> x ∈ A -> y ∈ A ->
  (A[R, x] = A[R, y] <-> ⟨x, y⟩ ∈ R).
Proof.
  intros R A x y P1 P2 P3.
  split.
  + intros P4.
    pose (equiv_class_intro_self R A y P1 P3) as P5.
    rewrite <- P4 in P5.
    apply (equiv_class_elim_1 _ _ _ _ P5).
  + intros P4.
    apply ax_exten.
    intros r.
    split.
    - intro P5.
      apply (equiv_class_intro_2 _ _ _ _ P1).
      pose (equiv_class_elim_2 _ _ _ _ P5) as P6.
      destruct P1 as [_ [_ [_ P1]]].
      apply (P1 _ _ _ P6 P4).
    - intro P5.
      apply (equiv_class_intro_1 _ _ _ _ P1).
      pose (equiv_class_elim_1 _ _ _ _ P5) as P6.
      destruct P1 as [_ [_ [_ P1]]].
      apply (P1 _ _ _ P4 P6).
Qed.

Lemma equiv_class_eq_intro: forall R A x y, y ∈ A[R, x] -> A[R, x] = A[R, y].
Proof.
  intros R A x y P1.
  apply subset_asym.
  split.
  + intros a P2.
    apply equiv_class_intro_1.
    - apply (equiv_class_elim_4 _ _ _ _ P1).
    - destruct (equiv_class_elim_4 _ _ _ _ P1) as [_ [_ [_ P3]]].
      apply (P3 _ _ _ (equiv_class_elim_2 _ _ _ _ P1) 
        (equiv_class_elim_1 _ _ _ _ P2)).
  + intros a P2.
    apply equiv_class_intro_1.
    - apply (equiv_class_elim_4 _ _ _ _ P1).
    - destruct (equiv_class_elim_4 _ _ _ _ P1) as [_ [_ [_ P3]]].
      apply (P3 _ _ _ (equiv_class_elim_1 _ _ _ _ P1) 
        (equiv_class_elim_1 _ _ _ _ P2)).
Qed.

Lemma equiv_class_eq_elim: forall R A x y, equiv_rel R A -> x ∈ A -> 
  A[R, x] = A[R, y] -> ⟨x, y⟩ ∈ R.
Proof.
  intros R A x y P1 P2 P3.
  pose (equiv_class_intro_self _ _ _ P1 P2) as P4.
  rewrite P3 in P4.
  apply (equiv_class_elim_2 _ _ _ _ P4).
Qed.

Lemma equiv_class_subset: forall R A x, equiv_rel R A -> x ∈ A -> 
  A[R, x] ⊆ A.
Proof.
  intros R A x P1 P2 r P3.
  apply (equiv_class_elim_3 _ _ _ _ P3).  
Qed.

(* Partition *)
Definition is_partition (A: set) (B: set) :=
  (forall x y, x ∈ A -> y ∈ A -> x <> y -> x ∩ y = ∅) /\ ∪(A) = B.

Definition equiv_part (R: set) (A: set) :=
  (subset_ctor (fun r => exists x, x ∈ A /\ r = A[R, x]) (𝒫(A))).

Notation "A [\ R ]" := (equiv_part R A) (at level 60, no associativity).

Lemma equiv_part_elim_1: forall x R A, x ∈ A[\ R] ->
  exists a, a ∈ A /\ x = A[R, a].
Proof.
  intros x R A P1.
  destruct (subset_elim _ _ _ P1) as [_ [a P2]].
  exists a.
  apply P2.
Qed.

Lemma equiv_part_elim_2: forall a x R A, a ∈ x -> x ∈ A[\ R] -> a ∈ A.
Proof.
  intros a x R A P1 P2.
  destruct (equiv_part_elim_1 _ _ _ P2) as [b [_ P3]].
  rewrite P3 in P1.
  apply (equiv_class_elim_3 _ _ _ _ P1).
Qed.

Lemma equiv_part_intro: forall x R A, equiv_rel R A -> x ∈ A -> 
  A[R, x] ∈ A[\ R].
Proof.
  intros x R A P1 P2.
  apply (subset_intro).
  + apply subset_in_power.
    apply (equiv_class_subset _ _ _ P1 P2).
  + exists x.
    split.
    - apply P2.
    - reflexivity.
Qed.

Lemma equiv_part_is_partition: forall R A, equiv_rel R A ->
  is_partition (A[\R]) A.
Proof.
  intros R A P1.
  split.
  + intros x y P2 P3 P4.
    apply empty_unique.
    intros a P5.
    absurd (x = y).
    - apply P4.
    - destruct (in_inter2_in _ _ _ P5) as [Q1 R1].
      destruct (equiv_part_elim_1 _ _ _ P2) as [b1 [Q2 Q3]].
      rewrite Q3 in Q1.
      rewrite Q3.
      rewrite (equiv_class_eq_intro _ _ _ _ Q1).
      destruct (equiv_part_elim_1 _ _ _ P3) as [b2 [R2 R3]].
      rewrite R3 in R1.
      rewrite R3.
      rewrite (equiv_class_eq_intro _ _ _ _ R1).
      reflexivity.
  + apply ax_exten.
    intros a.
    split.
    - intros P2.
      destruct (in_union_in _ _ P2) as [y [P3 P4]].
      apply (equiv_part_elim_2 _ _ _ _ P4 P3).
    - intros P2.
      apply in_in_union.
      exists (A[R, a]).
      split.
      * apply (equiv_part_intro _ _ _ P1 P2). 
      * apply (equiv_class_intro_self _ _ _ P1 P2).
Qed.
(*----------------------------------------------------------------------------*)
