Require Import axiom.axiom.
Require Import axiom.ax_infinity.
Require Import operation.basic.
Require Import nat.inductive.

(* Nature Number *)
Definition nat (n: set) := forall B, inductive B -> n ∈ B.

Theorem omega_exists: exists A, forall n, nat n <-> n ∈ A.
Proof.
  destruct ax_infinity as [X P1].
  exists (subset_ctor (fun n => forall B, inductive B -> n ∈ B) X). 
  intros n.
  split.
  + intros P2.
    apply subset_intro.
    - apply (P2 X P1).
    - intros B P3.
      apply (P2 B P3).
  + apply subset_elim.
Qed.

Definition omega := extract_set omega_exists.
Notation ω := omega.

Lemma omega_intro: forall x, nat x -> x ∈ ω.
Proof.
  intros x P1.
  destruct (extract_set_property omega_exists x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma omega_elim: forall x, x ∈ ω-> nat x.
Proof.
  intros x P1.
  destruct (extract_set_property omega_exists x) as [_ P2].
  apply (P2 P1).
Qed.

Lemma omega_is_inductive: inductive ω.
Proof.
  split.
  + apply omega_intro.
    intros A [P1 _].
    apply P1.
  + intros x P1.
    apply omega_intro.
    intros A P2.
    pose (omega_elim x P1 A P2) as P3.
    destruct P2 as [P4 P5].
    apply (P5 x P3).
Qed.

Lemma omega_subset_inductive: forall A, inductive A -> ω ⊆ A.
Proof.
  intros A P1 x P2.
  apply (omega_elim x P2 A P1).
Qed.

Lemma empty_in_omega: ∅ ∈ ω.
Proof.
  apply omega_intro.
  intros B P1.
  destruct P1 as [P2 _].
  apply P2.
Qed.

Lemma suc_in_omega: forall k, k ∈ ω -> S(k) ∈ ω.
Proof.
  intros k P1.
  destruct (omega_is_inductive) as [_ P2].
  apply (P2 _ P1).
Qed.
(*----------------------------------------------------------------------------*)

(* Induction Principle *)
Lemma inductive_subset_omega_coincident: forall T, T ⊆ ω -> inductive T -> 
  T = ω.
Proof.
  intros T P1 P2.
  apply subset_asym.
  apply (conj P1 (omega_subset_inductive T P2)).
Qed.

Definition induction_step (P: set -> Prop) :=
  (forall k, k ∈ ω -> P k -> P (S(k))).

Lemma induction_principle: forall P: set -> Prop, P ∅ ->
  induction_step P -> (forall n, n ∈ ω -> P n).
Proof.
  intros P P1 P2 n P3.
  assert ((subset_ctor P ω) ⊆ ω) as P4.
  { intros x P5.
    destruct (subset_elim _ _ _ P5) as [P6 _].
    apply P6. }
  assert (inductive (subset_ctor P ω)) as P5.
  { split.
    + apply (subset_intro _ _ _ (empty_in_omega) P1).
    + intros x P5.
      destruct (subset_elim _ _ _ P5) as [P6 P7].
      apply (subset_intro _ _ _ (suc_in_omega _ P6) (P2 _ P6 P7)). }
  rewrite <- (inductive_subset_omega_coincident _ P4 P5) in P3.
  destruct (subset_elim _ _ _ P3) as [_ P6].
  apply P6.
Qed.
(*----------------------------------------------------------------------------*)

(* More Natue Number Property *)
Lemma nat_is_suc: forall x, x ∈ ω -> x <> ∅ -> exists y, y ∈ ω /\ x = S(y).
Proof.
  intros x P1 P2.
  pose (P := fun x => x = ∅ \/ exists y, y ∈ ω /\ x = S(y)).
  assert (P ∅) as P3.
  { left.
    reflexivity. }
  assert (induction_step P) as P4.
  { intros k P5 [P4|P4].
    + right.
      exists ∅.
      rewrite P4.
      split.
      - apply empty_in_omega. 
      - reflexivity.
    + right.
      exists k.
      split.
      - apply P5. 
      - reflexivity. }
  destruct (induction_principle _ P3 P4 x P1) as [P5|P5].
  + contradiction.
  + apply P5.
Qed.

(* 4F *)
Lemma nat_is_trans: forall A, nat A -> trans A.
Proof.
  intros A P1.
  assert (induction_step trans) as P2.
  { intros k _ P2.
    apply trans_intro_1.
    rewrite (union_trans_suc _ P2).
    intros x P3.
    apply (suc_intro_2 _ _ P3). }
  apply (induction_principle _ (empty_is_trans) P2 A (omega_intro _ P1)).
Qed.

(* 4G *)
Lemma omega_is_trans: trans ω.
Proof. 
  assert (∅ ⊆ ω) as P1.
  { intros x P1.
    absurd (x ∈ ∅).
    + apply not_in_empty.
    + apply P1. }
  assert (induction_step (fun x => x ⊆ ω)) as P2.
  { intros k P2 P3 x P4.
    destruct (suc_elim _ _ P4) as [P5|P5].
    + rewrite P5.
      apply P2.
    + apply (P3 _ P5). }
  apply (trans_intro_2 _ (induction_principle _ P1 P2)).
Qed.

Lemma nat_not_in_self: forall n, n ∈ ω -> n ∉  n.
Proof.
  intros n P1.
  assert (∅ ∉  ∅) as P2.
  { apply not_in_empty. }
  assert (induction_step (fun x => x ∉ x)) as P3.
  { intros k P3 P4 P5.
    absurd (k ∈ k). 
    + apply P4.
    + destruct (suc_elim _ _ P5) as [P6|P6].
      - pose (P7 := suc_intro_1 k).
        rewrite P6 in P7.
        apply P7.
      - pose (P7 := suc_intro_1 k).
        apply (nat_is_trans _ (omega_elim _ P3) _ _ P7 P6). }
  apply (induction_principle _ P2 P3 _ P1).
Qed.

Lemma suc_unique: forall x y, x ∈ ω -> y ∈ ω -> S(x) = S(y) -> x = y.
Proof. 
  intros x y P1 P2 P3.
  pose (suc_intro_1 x) as P4.
  rewrite P3 in P4.
  destruct (suc_elim _ _ P4) as [P5|P5].
  + apply P5.
  + pose (suc_intro_1 y) as P6.
    rewrite <- P3 in P6.
    destruct (suc_elim _ _ P6) as [P7|P7].
    - symmetry. 
      apply P7.
    - absurd (x ∈ x). 
      * apply (nat_not_in_self _ P1). 
      * apply (nat_is_trans _ (omega_elim _ P1) _ _ P5 P7).
Qed.
(*----------------------------------------------------------------------------*)
