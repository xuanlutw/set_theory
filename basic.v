Require Import logic.
Require Import axiom.

Lemma subset_asym: forall A B, A ⊆ B /\ B ⊆ A -> A = B.
Proof.
  intros A B P1.
  apply ax_exten.
  intro x.
  destruct P1 as [P2 P3].
  split.
  + apply (P2 x).
  + apply (P3 x).
Qed.

Lemma subset_refl: forall A, A ⊆ A.
Proof.
  intros A x P.
  apply P.
Qed.

Lemma subset_trans: forall A B C, A ⊆ B -> B ⊆ C -> A ⊆ C.
Proof.
  intros A B C P1 P2 x P3.
  pose (P4 := P1 x).
  pose (P5 := P2 x).
  apply (P5 (P4 P3)).
Qed.

Lemma subset_in_in: forall A B x, A ⊆ B -> x ∈ A -> x ∈ B.
Proof.
  intros A B x P1 P2.
  apply (P1 x P2).
Qed.

Lemma eq_subset_1: forall A B, A = B -> A ⊆ B.
Proof.
  intros A B P1.
  rewrite P1.
  apply subset_refl.
Qed.

Lemma eq_subset_2: forall A B, A = B -> B ⊆ A.
Proof.
  intros A B P1.
  rewrite P1.
  apply subset_refl.
Qed.

Lemma exten_reverse: forall A B: set, A = B -> (forall x: set, x ∈  A <-> x ∈  B).
Proof.
  intros A B P1 x.
  rewrite P1.
  split.
  + intro P2. apply P2.
  + intro P2. apply P2.
Qed.

Lemma not_equal_exist: forall A B, A <> B -> 
  exists x, (x ∈ A /\ x ∉  B) \/ (x ∈ B /\ x ∉  A).
Proof.
  intros A B.
  apply contraposition2.
  intros P1.
  apply ax_exten.
  intros x.
  split.
  + intros P2. 
    destruct (not_or_and _ _ (not_exists_forall_not _ _ P1 x)) as [P3 P4].
    destruct (not_and_or _ _ P3) as [P5|P5].
    - contradiction.
    - apply (NN_elim _ P5). 
  + intros P2.
    destruct (not_or_and _ _ (not_exists_forall_not _ _ P1 x)) as [P3 P4].
    destruct (not_and_or _ _ P4) as [P5|P5].
    - contradiction.
    - apply (NN_elim _ P5). 
Qed.
      
Lemma subset_reduce: forall P: set -> Prop, forall A, 
  (forall x, (P x) -> x ∈ A) -> (exists B, forall y, y ∈ B <-> (P y)).
Proof.
  intros P A P1.
  pose (z := extract_set (ax_subset P A)).
  exists z.
  intros x.
  destruct (extract_set_property (ax_subset P A) x) as [P3 P4].
  split.
  + apply P3.
  + intros P5.
    apply P4.
    split.
    - apply (P1 x P5).
    - apply P5.
Qed.

Lemma subset_intro: forall P: set -> Prop, forall A x, x ∈ A -> (P x) -> 
  x ∈ subset_ctor P A.
Proof.
  intros P A x P1 P2.
  destruct (extract_set_property (ax_subset P A) x) as [_ P3].
  apply (P3 (conj P1 P2)).
Qed.

Lemma subset_elim: forall P: set -> Prop, forall A x, x ∈ (subset_ctor P A) ->
  x ∈ A /\ (P x).
Proof.
  intros P A x P1.
  destruct (extract_set_property (ax_subset P A) x) as [P2 _].
  apply (P2 P1).
Qed.
(* TODO rewrite other subset intro and elim *)
(*----------------------------------------------------------------------------*)


(* Empty Set *)
Lemma not_in_empty: forall A, A ∉  ∅.
Proof.
  intro A.
  apply (extract_set_property ax_empty A).
Qed.

Lemma empty_unique: forall A, (forall B, B ∉ A) -> A = ∅ .
Proof.
  intros A P1.
  apply ax_exten.
  intro x.
  pose (P2 := not_in_empty x).
  split.
  + intro P3. pose (P4 := P1 x). contradiction.
  + intro P3. contradiction.
Qed.

Lemma empty_subset: forall A, ∅ ⊆ A.
Proof.
  intros A x P1.
  absurd (x ∈ ∅).
  + apply (not_in_empty x).
  + apply P1.
Qed.

Lemma not_empty_exist_elmn: forall A, A <> ∅  -> (exists x, x ∈ A).
Proof.
  intros A.
  apply (contraposition2).
  intro P1.
  apply (empty_unique).
  apply (not_exists_forall_not set (set_in2 A)).
  apply P1.
Qed.
(*  apply *)
(*  assert ((~(exists (a: set), a ∈ A) -> A = ∅ )).*)
(*  intro.*)
(*  assert (forall a, a ∉ A).*)
(*  apply (not_exists_forall_not). assumption.*)
(*  apply (empty_unique). assumption.*)
(*  apply e.*)
(*  apply H.*)
(**)
(*  assert ((~(exists (a: set), a ∈ A) -> A = ∅ ) -> (A <> ∅ -> (exists a, a ∈ A))).*)
(*  apply (contraposition2).*)
(*  assert ((~(exists (a: set), a ∈ A) -> A = ∅ )).*)
(*  intro.*)
(*  assert (forall a, a ∉ A).*)
(*  apply (not_exists_forall_not). assumption.*)
(*  apply (empty_unique). assumption.*)
(*  apply e.*)
(*  apply H. *)
(*----------------------------------------------------------------------------*)


(* Power *)
Lemma in_powe_subsetr: forall A x, x ∈ 𝒫(A) -> x ⊆ A.
Proof.
  intros A x P1.
  destruct (extract_set_property (ax_power A) x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma subset_in_power: forall A x, x ⊆ A -> x ∈ 𝒫(A).
Proof.
  intros A x P1.
  destruct (extract_set_property (ax_power A) x) as [_ P2].
  apply (P2 P1).
Qed.

Lemma in_power: forall A, A ∈ 𝒫(A).
Proof.
  intros A.
  apply subset_in_power.
  apply subset_refl.
Qed.

(*----------------------------------------------------------------------------*)

(* Union *)
Lemma in_union_in: forall A x, x ∈ ∪(A) -> (exists y, y ∈ A /\ x ∈ y).
Proof.
  intros A x P1.
  destruct (extract_set_property (ax_union A) x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma in_in_union: forall A x, (exists y, y ∈ A /\ x ∈ y) -> x ∈ ∪(A).
Proof.
  intros A x P1.
  destruct (extract_set_property (ax_union A) x) as [_ P2].
  apply (P2 P1).
Qed.


(* Pair *)
Lemma singleton_basic: forall A, {A} = singleton(A).
Proof.
  intros A.
  apply ax_exten. 
  intro x. 
  destruct (extract_set_property (thm_union2 (singleton(A)) ∅) x) as [P1 P2].
  split.
  + intros P3.
    destruct (P1 P3) as [P4|P4].
    - apply P4.
    - absurd (x ∈ ∅).
      * apply ((extract_set_property ax_empty) x).
      * apply P4.
  + intro P3.
    apply P2.
    left.
    apply P3.
Qed.

Lemma in_singleton: forall A, A ∈ {A}.
Proof.
  intros A.
  rewrite (singleton_basic A).
  destruct (extract_set_property (ax_pair A A) A) as [_ P1].
  apply P1.
  left.
  reflexivity.
Qed.

Lemma in_singleton_equal: forall A B, B ∈ {A} -> A = B.
Proof.
  intros A B P1.
  destruct (extract_set_property (ax_pair A A) B) as [P2 _].
  rewrite (singleton_basic A) in P1.
  destruct (P2 P1) as [P3|P3].
  + rewrite P3. reflexivity.
  + rewrite P3. reflexivity.
Qed.

Lemma not_in_singleton: forall A B, A <> B -> B ∉  {A}.
Proof.
  intros A B.
  apply contraposition.
  apply in_singleton_equal.
Qed.

Lemma pair_basic: forall A B, {A, B} = pair_ctor A B. 
Proof.
  intros A B.
  apply ax_exten.
  intros x.
  pose (y := {B}).
  destruct (extract_set_property (thm_union2 (singleton(A)) y) x) as [P1 P2].
  destruct (extract_set_property (ax_pair A B) x) as [P3 P4].
  split.
  + intros P5.
    apply P4.
    destruct (P1 P5) as [P6|P6].
    - left. 
      symmetry. 
      rewrite <- (singleton_basic A) in P6.
      apply (in_singleton_equal A x P6).
    - right.
      symmetry. 
      apply (in_singleton_equal B x P6).
  + intros P5.
    apply P2.
    destruct (P3 P5) as [P6|P6].
    - left.
      rewrite P6.
      rewrite <- (singleton_basic).
      apply (in_singleton A).
    - right.
      rewrite P6.
      apply (in_singleton B).
Qed.
  
Lemma in_pair_equal: forall A B x, x ∈ {A, B} -> x = A \/ x = B.
Proof.
  intros A B x P1.
  rewrite pair_basic in P1.
  destruct (extract_set_property (ax_pair A B) x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma in_pair_1: forall A B, A ∈ {A, B}.
Proof.
  intros A B.
  rewrite pair_basic.
  destruct (extract_set_property (ax_pair A B) A) as [_ P2].
  apply P2.
  left.
  reflexivity.
Qed.

Lemma in_pair_2: forall A B, B ∈ {A, B}.
Proof.
  intros A B.
  rewrite pair_basic.
  destruct (extract_set_property (ax_pair A B) B) as [_ P2].
  apply P2.
  right.
  reflexivity.
Qed.

Lemma pair_sym: forall A B, {A, B} = {B, A}.
Proof.
  intros A B.
  apply ax_exten.
  intro x.
  split.
  + intro P1.
    destruct (in_pair_equal A B x P1) as [P2|P2].
    - rewrite P2.
      apply in_pair_2.
    - rewrite P2.
      apply in_pair_1.
  + intro P1.
    destruct (in_pair_equal B A x P1) as [P2|P2].
    - rewrite P2.
      apply in_pair_2.
    - rewrite P2.
      apply in_pair_1.
Qed.

Lemma pair_pair_equal_1: forall A B C D, {A, B} = {C, D} -> A = C \/ A = D.
Proof.
  intros A B C D P1.
  pose (P2 := in_pair_1 A B).
  rewrite P1 in P2.
  apply (in_pair_equal C D A P2).
Qed.

Lemma pair_pair_equal_2: forall A B C D, {A, B} = {C, D} -> B = C \/ B = D.
Proof.
  intros A B C D.
  rewrite (pair_sym A B).
  apply (pair_pair_equal_1).
Qed.

Lemma singleton_pair_equal_1: forall A B C, {A} = {B, C} -> A = B.
Proof.
  intros A B C P1.
  pose (P2 := in_pair_1 B C).
  rewrite <- P1 in P2.
  apply (in_singleton_equal A B P2).
Qed.

Lemma singleton_pair_equal_2: forall A B C, {A} = {B, C} -> A = C.
Proof.
  intros A B C P1.
  pose (P2 := in_pair_2 B C).
  rewrite <- P1 in P2.
  apply (in_singleton_equal A C P2).
Qed.

Lemma singleton_pair_equal_3: forall A B C, {A} = {B, C} -> B = C.
Proof.
  intros A B C P1.
  rewrite <- (singleton_pair_equal_1 A B C P1).
  apply (singleton_pair_equal_2 A B C P1).
Qed.

Lemma singleton_equal: forall A B, {A} = {B} -> A = B.
Proof.
  intros A B P1.
  pose (P2 := in_singleton A).
  symmetry.
  rewrite P1 in P2.
  apply (in_singleton_equal B A P2).
Qed.
(*----------------------------------------------------------------------------*)

(* Union *)
Lemma in_union2_in: forall A B x, x ∈ A ∪ B -> x ∈ A \/ x ∈ B.
Proof.
  intros A B x P1.
  destruct (extract_set_property (thm_union2 A B) x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma in_in_union2_1: forall A B x, x ∈ A -> x ∈ A ∪ B.
Proof.
  intros A B x P1.
  destruct (extract_set_property (thm_union2 A B) x) as [_ P2].
  apply P2.
  left.
  apply P1.
Qed.

Lemma in_in_union2_2: forall A B x, x ∈ B -> x ∈ A ∪ B.
Proof.
  intros A B x P1.
  destruct (extract_set_property (thm_union2 A B) x) as [_ P2].
  apply P2.
  right.
  apply P1.
Qed.

Lemma union2_sym: forall A B, A ∪ B = B ∪ A.
Proof.
  intros A B.
  apply ax_exten.
  intro x.
  split.
  + intro P1.
    destruct (in_union2_in A B x P1) as [P2|P2].
    - apply (in_in_union2_2).
      apply P2.
    - apply (in_in_union2_1).
      apply P2.
  + intro P1.
    destruct (in_union2_in B A x P1) as [P2|P2].
    - apply (in_in_union2_2).
      apply P2.
    - apply (in_in_union2_1).
      apply P2.
Qed.

(*----------------------------------------------------------------------------*)


(* inter2 *)
Lemma in_inter2_in: forall A B x, x ∈ A ∩ B -> x ∈ A /\ x ∈ B.
Proof.
  intros A B x P1.
  destruct (extract_set_property (thm_inter2 A B) x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma in_in_inter2: forall A B x, x ∈ A -> x ∈ B -> x ∈ A ∩ B.
Proof.
  intros A B x P1 P2.
  destruct (extract_set_property (thm_inter2 A B) x) as [_ P3].
  apply P3.
  split.
  + apply P1.
  + apply P2.
Qed.

Lemma inter2_sym: forall A B, A ∩ B = B ∩ A.
Proof.
  intros A B.
  apply ax_exten.
  intro x.
  split.
  + intro P1.
    destruct (in_inter2_in A B x P1) as [P2 P3].
    apply in_in_inter2.
    - apply P3.
    - apply P2.
  + intro P1.
    destruct (in_inter2_in B A x P1) as [P2 P3].
    apply in_in_inter2.
    - apply P3.
    - apply P2.
Qed.
  
Lemma inter2_in_1: forall A B, A ∩ B ⊆ A.
Proof.
  intros A B x P1.
  destruct (in_inter2_in A B x P1) as [P2 _].
  apply P2.
Qed.

Lemma inter2_in_2: forall A B, A ∩ B ⊆ B.
Proof.
  intros A B.
  rewrite (inter2_sym A B).
  apply inter2_in_1.
Qed.

Lemma subset_inter2: forall A B C, C ⊆ A -> C ⊆ B -> C ⊆ A ∩ B.
Proof.
  intros A B C P1 P2 x P3.
  apply in_in_inter2.
  + apply (P1 x P3).
  + apply (P2 x P3).
Qed.

Lemma inter2_subset_1: forall A B C, C ⊆ A ∩ B -> C ⊆ A.
Proof.
  intros A B C P1 x P2.
  destruct (in_inter2_in A B x (P1 x P2)) as [P3 _].
  apply P3.
Qed.
 
Lemma inter2_subset_2: forall A B C, C ⊆ A ∩ B -> C ⊆ B.
Proof.
  intros A B C.
  rewrite (inter2_sym A B).
  apply inter2_subset_1.
Qed.
(*----------------------------------------------------------------------------*)

(* Complement *)
Definition complement (A: set) (B: set) :=
  (subset_ctor (fun s => s ∉  B) A). 

Lemma complement_intro: forall A B x, x ∈ A /\ x ∉  B -> x ∈ complement A B.
Proof.
  intros A B x [P1 P2].
  destruct (extract_set_property (ax_subset (fun s => s ∉  B) A) x) as [_ P3].
  apply P3.
  apply (conj P1 P2).
Qed.

Lemma complement_elim: forall A B x, x ∈ complement A B -> x ∈ A /\ x ∉  B.
Proof.
  intros A B x P1.
  destruct (extract_set_property (ax_subset (fun s => s ∉  B) A) x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma complement_inter2: forall A B, A ∩ (complement B A) = ∅.
Proof.
  intros A B.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (in_inter2_in _ _ _ P1) as [P2 P3].
    destruct (complement_elim _ _ _ P3) as [_ P4].
    contradiction.
  + intros P1.
    pose (not_in_empty x).
    contradiction.
Qed.

Lemma complement_union2: forall A B, A ∪ (complement B A) = A ∪ B.
Proof.
  intros A B.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (in_union2_in _ _ _ P1) as [P2|P2].
    - apply (in_in_union2_1 _ _ _ P2).
    - destruct (complement_elim _ _ _ P2) as [P3 _].
      apply (in_in_union2_2 _ _ _ P3).
  + intros P1.
    destruct (in_union2_in _ _ _ P1) as [P2|P2].
    - apply (in_in_union2_1 _ _ _ P2).
    - destruct (LEM (x ∈ A)) as [P3|P3].
      * apply (in_in_union2_1 _ _ _ P3).
      * apply in_in_union2_2.
        apply complement_intro.
        apply (conj P2 P3).
Qed.

Lemma complement_proper_subset: forall A B, A ⊆ B -> A <> B -> exists x, x ∈ complement B A.
Proof. 
  intros A B P1 P2.
  destruct (not_equal_exist _ _ P2) as [x [[P3 P4]|P3]].
  exists x.
  + absurd (x ∈ B). 
    - apply P4.
    - apply (P1 _ P3).
  + exists x.
    apply (complement_intro _ _ _ P3).
Qed.
    
