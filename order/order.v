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
Definition po (R: set) (A: set) := r_trans R /\ r_irrefl R A.
Notation " x <[ R ] y" := (⟨x, y⟩ ∈ R) (at level 63, left associativity).
Notation " x ≤[ R ] y" := 
  (⟨x, y⟩ ∈ R \/ x = y) (at level 63, left associativity).

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

(* Well Order *)
Definition l_elmn (R: set) (A: set) (s: set) := forall x, x ∈ A -> s ≤[R] x.
Definition l_bound (R: set) (A: set) := exists x, x ∈ A /\ l_elmn R A x. 
Definition least_elmn (R: set) (A: set) := forall S, S ⊆ A -> S <> ∅ -> 
  l_bound R S.

Definition wo (R: set) (A: set) := lo R A /\ least_elmn R A.

Lemma wo_is_lo: forall R A, wo R A -> lo R A.
Proof.
  intros R A [P1 _].
  apply P1.
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

Definition seg (R: set) (A: set) (a: set) := subset_ctor (fun x => x <[R] a) A.
Definition l_inductive (R: set) (A: set) (B: set) := 
  B ⊆ A /\ forall t, t ∈ A -> seg R A t ⊆ B -> t ∈ B.

Theorem transfinite_induction: forall R A B, wo R A -> l_inductive R A B ->
  A = B.
Proof.
  intros R A B P1 [P2 P3].
  destruct (subset_elim_3 _ _ P2) as [P4|P4].
  + destruct P1 as [P1 P5].
    destruct (P5 (A \ B) (complement_subset A B) 
      (complement_proper_subset_nonempty _ _ P4)) as [x [P6 P7]].
    destruct (complement_elim _ _ _ P6) as [P8 P9].
    absurd (x ∈ B).
    - apply P9.
    - apply (P3 _ P8).
      intros y Q1.
      destruct (subset_elim _ _ _ Q1) as [Q2 Q3].
      destruct (complement_dilemma A B y Q2) as [Q4|Q4].
      * destruct (in_inter2_in _ _ _ Q4) as [_ Q5].
        apply Q5.
      * pose (wo_le _ _ _ _ (conj P1 P5) P8 Q2 (P7 _ Q4)).
        contradiction.
  + symmetry.
    apply P4.
Qed.
(* Skip 7C *)

Theorem transfinite_recursion: forall (G: set -> set -> Prop) R A, wo R A ->
  (forall x, exists y, (G x y) /\ (forall z, (G x z) -> y = z)) ->
  exists f, function f /\ dom(f) = A /\ 
  (forall t, t ∈ A -> (G (f↾ (seg R A t)) (f[t]))).
Proof.
Admitted.

Theorem epsilon_image_exist: forall R A, exists E, wo R A ->
  function E /\ dom(E) = A /\ (forall t, t ∈ A -> E[t] = E[|seg R A t|]). 
Proof.
  intros R A.
  destruct (LEM (wo R A)) as [P1|P1].
  + assert (forall x, exists y, y = ran(x) /\ (forall z, z = ran(x) -> 
      y = z)) as P2.
    { intros x.
      exists (ran(x)).
      split.
      + reflexivity. 
      + intros z P2. 
        symmetry.
        apply P2. }
    destruct (transfinite_recursion (fun x y => y = ran(x)) _ _ P1 P2) 
      as [E [P3 [P4 P5]]].
    exists E.
    intros _.
    split.
    - apply P3.
    - split.
      apply P4.
      apply P5.
  + exists R.
    intros P2.
    contradiction.
Qed.

Definition epsilon (R: set) (A: set) := extract_set (epsilon_image_exist R A).
Definition epsilon_image (R: set) (A: set) := ran(epsilon R A).

