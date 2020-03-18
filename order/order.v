Require Import axiom.axiom.
Require Import axiom.logic.
Require Import operation.basic.
Require Import relation.relation.
Require Import relation.function.
Require Import relation.util_function.
Require Import relation.equiv.

(* Partial Order *)
Definition po (R: set) (A: set) := r_trans R /\ r_irrefl R A.
Notation " x <[ R ] y" := (⟨x, y⟩ ∈ R) (at level 63, left associativity).
Notation " x ≤[ R ] y" := (⟨x, y⟩ ∈ R \/ x = y) (at level 63, left associativity).

Definition trichotomy (R: set) (A: set) := forall x y, x ∈ A -> y ∈ A ->
  ( x <[R] y /\ x <> y /\ ~y <[R] x) \/ 
  (~x <[R] y /\ x =  y /\ ~y <[R] x) \/ 
  (~x <[R] y /\ x <> y /\  y <[R] x).

Lemma po_trans: forall R A, po R A -> r_trans R.
Proof.
  intros R A P1.
  destruct P1 as [P1 _].
  apply P1.
Qed.

Lemma po_irrefl: forall R A, po R A -> r_irrefl R A.
Proof.
  intros R A P1.
  destruct P1 as [_ P1].
  apply P1.
Qed.

Lemma po_weak_at_most_1: forall R A x y, po R A -> x ∈ A -> y ∈ A ->
  ~(x <[R] y /\ x = y).
Proof.
  intros R A x y P1 P2 P3 [P4 P5].
  rewrite P5 in P4.
  pose (po_irrefl _ _ P1 _ P3).
  contradiction.
Qed.

Lemma po_weak_at_most_2: forall R A x y, po R A -> x ∈ A -> y ∈ A ->
  ~(y <[R] x /\ x = y).
Proof.
  intros R A x y P1 P2 P3 [P4 P5].
  rewrite P5 in P4.
  pose (po_irrefl _ _ P1 _ P3).
  contradiction.
Qed.

Lemma po_weak_at_most_3: forall R A x y, po R A -> x ∈ A -> y ∈ A ->
  ~(x <[R] y /\ y <[R] x).
Proof.
  intros R A x y P1 P2 P3 [P4 P5].
  pose (po_trans _ _ P1 _ _ _ P4 P5).
  pose (po_irrefl _ _ P1 _ P2).
  contradiction.
Qed.

Lemma po_sandwich: forall R A x y, po R A -> x ∈ A -> y ∈ A -> 
  x ≤[R] y -> y ≤[R] x -> x = y.
Proof.
  intros R A x y P1 P2 P3 P4 P5.
  destruct P4 as [P4|P4].
  + destruct P5 as [P5|P5].
    - pose (po_trans _ _ P1 _ _ _ P4 P5) as P6.
      pose (po_irrefl _ _ P1 _ P2) as P7.
      contradiction.
    - symmetry.
      apply P5.
  + apply P4.
Qed.

(* Linear Order *)
Definition lo (R: set) (A: set) := r_trans R /\ trichotomy R A.

Lemma lo_is_po: forall R A, lo R A -> po R A.
Proof.
  intros R A [P1 P2].
  split.
  + apply P1.
  + intros x P3.
    destruct (P2 _ _ P3 P3) as [P4|[P4|P4]].
    * destruct P4 as [_ [_ P4]].
      apply P4.
    * destruct P4 as [_ [_ P4]].
      apply P4.
    * destruct P4 as [P4 _].
      apply P4.
Qed.

Lemma lo_irrefl: forall R A, lo R A -> r_irrefl R A.
Proof.
  intros R A P1.
  apply (po_irrefl _ _ (lo_is_po _ _ P1)).
Qed.

Lemma lo_trans: forall R A, lo R A -> r_trans R.
  intros R A P1.
  apply (po_trans _ _ (lo_is_po _ _ P1)).
Qed.

Lemma lo_trichotomy: forall R A, lo R A -> trichotomy R A.
Proof.
  intros R A P1.
  destruct P1 as [_ P1].
  apply P1.
Qed.

Lemma lo_neq_elim: forall R A x y, lo R A -> x ∈ A -> y ∈ A -> x <> y ->
  (x <[R] y) \/ (y <[R] x).
Proof.
  intros R A x y P1 P2 P3 P4.
  destruct (lo_trichotomy _ _ P1 _ _ P2 P3) as [P5|[P5|P5]].
  + destruct P5 as [P5 [_ P6]].
    left.
    apply (conj P5 P6).
  + destruct P5 as [_ [P5 _]].
    contradiction.
  + destruct P5 as [P5 [_ P6]].
    right.
    apply (conj P5 P6).
Qed.

Lemma lo_neq_intro_1: forall R A x y, lo R A -> x ∈ A -> y ∈ A -> x <[R] y -> x <> y.
Proof.
  intros R A x y P1 P2 P3 P4.
  destruct (lo_trichotomy _ _ P1 _ _ P2 P3) as [P5|[P5|P5]].
  + destruct P5 as [_ [P5 _]].
    apply P5.
  + destruct P5 as [P5 _]. 
    contradiction.
  + destruct P5 as [_ [P5 _]].
    apply P5.
Qed.

Lemma lo_neq_intro_2: forall R A x y, lo R A -> x ∈ A -> y ∈ A -> y <[R] x -> x <> y.
Proof.
  intros R A x y P1 P2 P3 P4.
  destruct (lo_trichotomy _ _ P1 _ _ P2 P3) as [P5|[P5|P5]].
  + destruct P5 as [_ [P5 _]].
    apply P5.
  + destruct P5 as [_ [_ P5]]. 
    contradiction.
  + destruct P5 as [_ [P5 _]].
    apply P5.
Qed.

(* Well Order *)
Definition least_elmn (R: set) (A: set) := forall S, S ⊆ A -> S <> ∅ -> exists x, x ∈ S -> 
  forall y, y ∈ S -> x ≤[R] y.

Definition wo (R: set) (A: set) := lo R A /\ least_elmn R A.
