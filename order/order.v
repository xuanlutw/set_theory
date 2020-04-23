Require Import axiom.axiom.
Require Import axiom.logic.
Require Import operation.basic.
Require Import relation.relation.
Require Import relation.function.
Require Import relation.util_function.
Require Import relation.equiv.
Require Import nat.inductive.
Require Import nat.nat.

(* Partial Order *)
Definition po (R: set) (A: set) := r_trans R A /\ r_irrefl R A.
Notation " x <[ R ] y" := (⟨x, y⟩ ∈ R) (at level 63, left associativity).
Notation " x ≤[ R ] y" := 
  (⟨x, y⟩ ∈ R \/ x = y) (at level 63, left associativity).

Definition trichotomy (R: set) (A: set) := forall x y, x ∈ A -> y ∈ A ->
  ( x <[R] y /\ x <> y /\ ~y <[R] x) \/ 
  (~x <[R] y /\ x =  y /\ ~y <[R] x) \/ 
  (~x <[R] y /\ x <> y /\  y <[R] x).

Definition trichotomy_weak (R: set) (A: set) := forall x y, x ∈ A -> y ∈ A ->
  ( x <[R] y \/ x = y \/ y <[R] x).

Lemma po_trans: forall R A, po R A -> r_trans R A.
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
  pose (po_trans _ _ P1 _ _ _ P2 P3 P2 P4 P5).
  pose (po_irrefl _ _ P1 _ P2).
  contradiction.
Qed.

Lemma po_sandwich: forall R A x y, po R A -> x ∈ A -> y ∈ A -> 
  x ≤[R] y -> y ≤[R] x -> x = y.
Proof.
  intros R A x y P1 P2 P3 P4 P5.
  destruct P4 as [P4|P4].
  + destruct P5 as [P5|P5].
    - pose (po_trans _ _ P1 _ _ _ P2 P3 P2 P4 P5) as P6.
      pose (po_irrefl _ _ P1 _ P2) as P7.
      contradiction.
    - symmetry.
      apply P5.
  + apply P4.
Qed.
(*----------------------------------------------------------------------------*)

(* Linear Order *)
Definition lo (R: set) (A: set) := r_trans R A /\ trichotomy R A.

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

Lemma lo_trans: forall R A, lo R A -> r_trans R A.
  intros R A P1.
  apply (po_trans _ _ (lo_is_po _ _ P1)).
Qed.

Lemma lo_trichotomy: forall R A, lo R A -> trichotomy R A.
Proof.
  intros R A P1.
  destruct P1 as [_ P1].
  apply P1.
Qed.

Lemma lo_trichotomy_weak: forall R A, lo R A -> trichotomy_weak R A.
Proof.
  intros R A P1 x y P2 P3.
  destruct (lo_trichotomy _ _ P1 _ _ P2 P3) as [[Q1 _]|[[_ [Q1 _]]|[_ [_ Q1]]]].
  + left.
    apply Q1.
  + right. left.
    apply Q1.
  + right. right.
    apply Q1.
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

Lemma lo_neq_intro_1: forall R A x y, lo R A -> x ∈ A -> y ∈ A -> x <[R] y -> 
  x <> y.
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

Lemma lo_neq_intro_2: forall R A x y, lo R A -> x ∈ A -> y ∈ A -> y <[R] x -> 
  x <> y.
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

Lemma lo_not_less: forall R A x y, lo R A -> x ∈ A -> y ∈ A -> ~(x <[R] y) ->
  y ≤[R] x.
Proof.
  intros R A x y P1 P2 P3 P4.
  destruct (lo_trichotomy _ _ P1 _ _ P2 P3) as [P5|[P5|P5]].
  + destruct P5 as [P5 _].
    contradiction.
  + destruct P5 as [_ [P5 _]].
    right.
    symmetry.
    apply P5.
  + destruct P5 as [_ [_ P5]].
    left.
    apply P5.
Qed.

Lemma lo_le: forall R A x y, lo R A -> x ∈ A -> y ∈ A -> x ≤[R] y ->
  ~(y <[R] x).
Proof.
  intros R A x y P1 P2 P3 [P4|P4].
  + destruct (lo_trichotomy _ _ P1 _ _ P3 P2) as [P5|[P5|P5]].
    - destruct P5 as [_ [_ P5]].
      contradiction.
    - destruct P5 as [P5 _].
      apply P5.
    - destruct P5 as [P5 _].
      apply P5.
  + destruct (lo_trichotomy _ _ P1 _ _ P3 P2) as [P5|[P5|P5]].
    - destruct P5 as [_ [P5 _]].
      symmetry in P4.
      contradiction.
    - destruct P5 as [P5 _].
      apply P5.
    - destruct P5 as [P5 _].
      apply P5.
Qed.

Lemma lo_not_le: forall R A x y, lo R A -> x ∈ A -> y ∈ A -> ~(x ≤[R] y) ->
  y <[R] x.
Proof.
  intros R A x y P1 P2 P3 P4.
  destruct (not_or_and _ _ P4) as [P5 P6].
  destruct (lo_trichotomy _ _ P1 _ _ P2 P3) as [P7|[P7|P7]].
  + destruct P7 as [P7 _].
    contradiction.
  + destruct P7 as [_ [P7 _]].
    contradiction.
  + destruct P7 as [_ [_ P7]].
    apply P7.
Qed.

Lemma lo_less: forall R A x y, lo R A -> x ∈ A -> y ∈ A -> x <[R] y ->
  ~(y ≤[R] x).
Proof.
  intros R A x y P1 P2 P3 P4.
  apply and_not_or.
  split.
  + destruct (lo_trichotomy _ _ P1 _ _ P3 P2) as [P5|[P5|P5]].
    - destruct P5 as [_ [_ P5]].
      contradiction.
    - destruct P5 as [_ [_ P5]].
      contradiction.
    - destruct P5 as [P5 _].
      apply P5.
  + destruct (lo_trichotomy _ _ P1 _ _ P3 P2) as [P5|[P5|P5]].
    - destruct P5 as [_ [P5 _]].
      apply P5.
    - destruct P5 as [_ [_ P5]].
      contradiction.
    - destruct P5 as [_ [P5 _]].
      apply P5.
Qed.
(*----------------------------------------------------------------------------*)

(* Well Order *)
Definition l_elmn (R: set) (A: set) (s: set) := forall x, x ∈ A -> s ≤[R] x.
Definition l_bound (R: set) (A: set) := exists x, x ∈ A /\ l_elmn R A x. 
Definition least_elmn (R: set) (A: set) := forall S, S ⊆ A -> S <> ∅ -> 
  l_bound R S.

Definition wo (R: set) (A: set) := lo R A /\ least_elmn R A.

Lemma wo_least_elmn: forall R A, wo R A -> least_elmn R A.
Proof.
  intros R A [_ P1].
  apply P1.
Qed.

Lemma wo_is_lo: forall R A, wo R A -> lo R A.
Proof.
  intros R A [P1 _].
  apply P1.
Qed.

Lemma wo_trichotomy: forall R A, wo R A -> trichotomy R A.
Proof.
  intros R A P1.
  apply lo_trichotomy.
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_trichotomy_weak: forall R A, wo R A -> trichotomy_weak R A.
Proof.
  intros R A P1.
  apply lo_trichotomy_weak.
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_neq_elim: forall R A x y, wo R A -> x ∈ A -> y ∈ A -> x <> y ->
  (x <[R] y) \/ (y <[R] x).
Proof.
  intros R A x y P1.
  apply lo_neq_elim.
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_neq_intro_1: forall R A x y, wo R A -> x ∈ A -> y ∈ A -> x <[R] y -> 
  x <> y.
Proof.
  intros R A x y P1.
  apply lo_neq_intro_1.
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_not_less: forall R A x y, wo R A -> x ∈ A -> y ∈ A -> ~(x <[R] y) ->
  y ≤[R] x.
Proof.
  intros R A x y P1.
  apply lo_not_less. 
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_le: forall R A x y, wo R A -> x ∈ A -> y ∈ A -> x ≤[R] y ->
  ~(y <[R] x).
Proof.
  intros R A x y P1.
  apply lo_le.
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_not_le: forall R A x y, wo R A -> x ∈ A -> y ∈ A -> ~(x ≤[R] y) ->
  y <[R] x.
Proof.
  intros R A x y P1.
  apply lo_not_le. 
  apply (wo_is_lo _ _ P1).
Qed.

Lemma wo_less: forall R A x y, wo R A -> x ∈ A -> y ∈ A -> x <[R] y ->
  ~(y ≤[R] x).
Proof.
  intros R A x y P1.
  apply lo_less.
  apply (wo_is_lo _ _ P1).
Qed.

Lemma no_descending: forall R A f, wo R A -> fover f ω A -> 
  ~(forall n, n ∈ ω -> f[S(n)] <[R] f[n]).
Proof.
  intros R A f P1 P2 P3.
  absurd (l_bound R (ran(f))).
  + intros P4.
    destruct P4 as [x [Q1 Q2]].
    destruct (ran_elim _ _ Q1) as [n Q3].
    absurd (x ≤[R] f[S(n)]).
    - apply (wo_less _ _ _ _ P1).
      * destruct P2 as [Q4 [Q5 Q6]].
        apply Q6.
        apply (fval_ran _ _ Q4).
        rewrite Q5.
        apply (suc_is_nat).
        rewrite <- Q5.
        apply (dom_intro_2 _ _ _ Q3).
      * destruct P2 as [_ [_ P2]].
        apply (P2 _ Q1).
      * destruct P2 as [P2 [P4 _]].
        rewrite (fval_intro _ _ _ P2 Q3).
        apply P3.
        rewrite <- P4.
        apply (dom_intro_2 _ _ _ Q3).
    - apply Q2.
      apply fval_ran.
      * destruct  P2 as [P2 _].
        apply P2.
      * destruct  P2 as [_ [P2 _]].
        rewrite P2.
        apply (suc_is_nat).
        rewrite <- P2.
        apply (dom_intro_2 _ _ _ Q3).
  + destruct P1 as [_ P1].
    apply P1.
    - destruct P2 as [_ [_ P2]].
      apply P2.
    - apply nonempty_dom_nonempty_ran.
      * destruct P2 as [P2 _].
        apply P2.
      * destruct P2 as [_ [P2 _]].
        rewrite P2.
        apply nat_nonempty.
Qed.
(* Skip reverse *)
(*----------------------------------------------------------------------------*)

(* Subset *)
Lemma subset_r_irrefl: forall R A B, r_irrefl R A -> B ⊆ A -> r_irrefl R B.
Proof.
  intros R A B P1 P2 x P3.
  apply (P1 _ (P2 _ P3)).
Qed.

Lemma subset_r_trans: forall R A B, r_trans R A -> B ⊆ A -> r_trans R B.
Proof.
  intros R A B P1 P2 x y z P3 P4 P5.
  apply (P1 _ _ _ (P2 _ P3) (P2 _ P4) (P2 _ P5)).
Qed.

Lemma subset_trichotomy: forall R A B, trichotomy R A -> B ⊆ A -> 
  trichotomy R B.
Proof.
  intros R A B P1 P2 x y P3 P4.
  apply (P1 _ _ (P2 _ P3) (P2 _ P4)).
Qed.

Lemma subset_least_elmn: forall R A B, least_elmn R A -> B ⊆ A -> 
  least_elmn R B.
Proof.
  intros R A B P1 P2 x P3 P4.
  apply (P1 _ (subset_trans _ _ _ P3 P2) P4).
Qed.
  
Lemma po_subset: forall R A B, po R A -> B ⊆ A -> po R B.
Proof.
  intros R A B [P1 P2] P3.
  split.
  + apply (subset_r_trans _ _ _ P1 P3).
  + apply (subset_r_irrefl _ _ _ P2 P3).
Qed.

Lemma lo_subset: forall R A B, lo R A -> B ⊆ A -> lo R B.
Proof.
  intros R A B [P1 P2] P3.
  split.
  + apply (subset_r_trans _ _ _ P1 P3).
  + apply (subset_trichotomy _ _ _ P2 P3).
Qed.

Lemma wo_subset: forall R A B, wo R A -> B ⊆ A -> wo R B.
Proof.
  intros R A B [P1 P2] P3.
  split.
  + apply (lo_subset _ _ _ P1 P3).
  + apply (subset_least_elmn _ _ _ P2 P3).
Qed.
(*----------------------------------------------------------------------------*)
