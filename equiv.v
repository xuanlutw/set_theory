Require Import logic.
Require Import axiom.
Require Import basic.
Require Import relation.

Definition r_refl (R: set) (A: set) := forall a, a ∈ A -> ⟨a, a⟩ ∈ R.
Definition r_sym (R: set) := forall x y, ⟨x, y⟩ ∈ R -> ⟨y, x⟩ ∈ R.
Definition r_trans (R: set) := forall x y z, ⟨x, y⟩ ∈ R /\ ⟨y, z⟩ ∈ R -> ⟨x, z⟩ ∈ R.

Definition equiv_rel (R: set) (A:set) := 
  (relation_on R A) /\ (r_refl R A) /\ (r_sym R) /\ (r_trans R).

Lemma sym_trans_equive: forall R, relation R /\ r_sym R /\ r_trans R -> 
  equiv_rel R (fld(R)).
Proof.
  intros R [P1 [P2 P3]].
  split. 
  { intros r P4.
    destruct (P1 r P4) as [a [b P5]].
    exists a.
    exists b.
    split.
    + apply in_in_union2_1.
      apply domain_intro.
      exists b.
      rewrite <- P5.
      apply P4.
    + split.
      - apply in_in_union2_2.
        apply range_intro.
        exists a.
        rewrite <- P5.
        apply P4. 
      - apply P5. }
  split.
  { intros r Q1.
    destruct (in_union2_in _ _ _ Q1) as [Q2|Q2].
    + destruct (domain_elim _ _ Q2) as [s Q3].
      apply (P3 _ _ _ (conj Q3 (P2 _ _ Q3))).
    + destruct (range_elim _ _ Q2) as [s Q3].
      apply (P3 _ _ _ (conj (P2 _ _ Q3) Q3)). }
  split.
  { apply P2. }
  { apply P3. }
Qed.

Definition equiv_class (x: set) (R: set) (A: set) :=
  subset_ctor (fun r => x ∈ A /\ equiv_rel R A /\ ⟨x, r⟩ ∈ R) A.

Lemma equiv_class_intro_1: forall R A x y, equiv_rel R A -> ⟨x, y⟩ ∈ R -> y ∈ equiv_class x R A.
Proof.
  intros R A x y P1 P2.
  apply (subset_intro).
  + destruct P1 as [P1 _]. 
    destruct (P1 _ P2) as [a [b [_ [P3 P4]]]].
    rewrite (opair_equal_elim_2 _ _ _ _ P4).
    apply P3.
  + split.
    - destruct P1 as [P1 _]. 
      destruct (P1 _ P2) as [a [b [P3 [_ P4]]]].
      rewrite (opair_equal_elim_1 _ _ _ _ P4).
      apply P3.
    - split.
      * apply P1.
      * apply P2.
Qed.

Lemma equiv_class_intro_2: forall R A x y, equiv_rel R A -> ⟨y, x⟩ ∈ R -> y ∈ equiv_class x R A.
Proof.
  intros R A x y P1 P2.
  apply equiv_class_intro_1.
  + apply P1.
  + destruct P1 as [_ [_ [P1 _]]].
    apply (P1 _ _ P2).
Qed.

Lemma equiv_class_intro_self: forall R A x, equiv_rel R A -> x ∈ A -> x ∈ equiv_class x R A.
Proof.
  intros R A x P1 P2.
  apply equiv_class_intro_1.
  + apply P1.
  + destruct P1 as [_ [P1 _]].
    apply (P1 _ P2).
Qed.

Lemma equiv_class_elim_1: forall R A x y, y ∈ equiv_class x R A -> ⟨x, y⟩ ∈ R.
Proof.
  intros R A x y P1.
  destruct (subset_elim _ _ _ P1) as [_ [_ [_ P2]]].
  apply P2.
Qed.

Lemma equiv_class_elim_2: forall R A x y, y ∈ equiv_class x R A -> ⟨y, x⟩ ∈ R.
Proof.
  intros R A x y P1.
  destruct (subset_elim _ _ _ P1) as [_ [_ [[_ [_ [P3 _]]] P2]]].
  apply (P3 _ _ P2).
Qed.

Lemma equiv_class_elim_3: forall R A x y, y ∈ equiv_class x R A -> y ∈ A.
Proof.
  intros R A x y P1.
  destruct (subset_elim _ _ _ P1) as [P2 _].
  apply P2.
Qed.

Lemma equiv_class_eq: forall R A x y, equiv_rel R A -> x ∈ A -> y ∈ A ->
  (equiv_class x R A = equiv_class y R A <-> ⟨x, y⟩ ∈ R).
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
      apply (P1 _ _ _ (conj P6 P4)).
    - intro P5.
      apply (equiv_class_intro_1 _ _ _ _ P1).
      pose (equiv_class_elim_1 _ _ _ _ P5) as P6.
      destruct P1 as [_ [_ [_ P1]]].
      apply (P1 _ _ _ (conj P4 P6)).
Qed.

Lemma equiv_class_subset: forall R A x, equiv_rel R A -> x ∈ A -> equiv_class x R A ⊆ A.
Proof.
  intros R A x P1 P2 r P3.
  apply (equiv_class_elim_3 _ _ _ _ P3).  
Qed.

Definition is_partition (A: set) (B: set) :=
  (forall x y, x ∈ A -> y ∈ A -> x <> y -> x ∩ y = ∅) /\ ∪(A) = B.

Lemma equiv_class_partition: forall R A, equiv_rel R A ->
  is_partition (subset_ctor 
    (fun r => exists x, x ∈ A /\ r = equiv_class x R A) (𝒫(A))) A.
Proof.
  intros R A P1.
  split.
  + intros x y P2 P3 P4.
    apply empty_unique.
    intros a P5.
    absurd (x = y).
    - apply P4.
    - destruct (subset_elim _ _ _ P2) as [_ [xx [_ P6]]].
      destruct (subset_elim _ _ _ P3) as [_ [yy [_ P7]]].
      destruct (in_inter2_in _ _ _ P5) as [P8 P9].
      rewrite P6 in P8.
      rewrite P7 in P9.
      apply ax_exten.
      intros r.
      split.
      * intros P10.
        rewrite P7.
        apply (equiv_class_intro_1 _ _ _ _ P1).
        rewrite P6 in P10.
        pose (equiv_class_elim_1 _ _ _ _ P10) as P11.
        pose (equiv_class_elim_2 _ _ _ _ P8) as P12.
        pose (equiv_class_elim_1 _ _ _ _ P9) as P13.
        destruct P1 as [_ [_ [_ P1]]].
        apply (P1 _ _ _ (conj (P1 _ _ _ (conj P13 P12)) P11)).
      * intros P10.
        rewrite P6.
        apply (equiv_class_intro_1 _ _ _ _ P1).
        rewrite P7 in P10.
        pose (equiv_class_elim_1 _ _ _ _ P10) as P11.
        pose (equiv_class_elim_1 _ _ _ _ P8) as P12.
        pose (equiv_class_elim_2 _ _ _ _ P9) as P13.
        destruct P1 as [_ [_ [_ P1]]].
        apply (P1 _ _ _ (conj (P1 _ _ _ (conj P12 P13)) P11)).
  + apply ax_exten.
    intros a.
    split.
    - intros P2.
      destruct (in_union_in _ _ P2) as [y [P3 P4]].
      destruct (subset_elim _ _ _ P3) as [P5 _].
      apply (in_power_subset _ _ P5 _ P4).
    - intros P2.
      apply in_in_union.
      exists (equiv_class a R A).
      split.
      * apply subset_intro.
        { apply subset_in_power.
          apply (equiv_class_subset _ _ _ P1 P2). }
        { exists a.
          split.
          + apply P2.
          + reflexivity. }
      * apply (equiv_class_intro_self _ _ _ P1 P2).
Qed.
