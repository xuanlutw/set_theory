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

(* Initial Segment *)
Definition seg (R: set) (A: set) (a: set) := subset_ctor (fun x => x <[R] a) A.
Definition l_inductive (R: set) (A: set) (B: set) := 
  B ⊆ A /\ forall t, t ∈ A -> seg R A t ⊆ B -> t ∈ B.

Lemma seg_intro: forall R A x y, y ∈ A -> y <[R] x -> y ∈ (seg R A x).
Proof.
  intros R A x y P1 P2.
  apply subset_intro.
  + apply P1.
  + apply P2.
Qed.

Lemma seg_elim_1: forall R A x y, x ∈ A -> y ∈ (seg R A x) -> y ∈ A.
Proof.
  intros R A x y P1 P2.
  destruct (subset_elim _ _ _ P2) as [P3 P4].
  apply P3.
Qed.

Lemma seg_elim_2: forall R A x y, x ∈ A -> y ∈ (seg R A x) -> y <[R] x.
Proof.
  intros R A x y P1 P2.
  destruct (subset_elim _ _ _ P2) as [P3 P4].
  apply P4.
Qed.
(*----------------------------------------------------------------------------*)

(* Transfinite *)
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
(* Skip unique *)
(*----------------------------------------------------------------------------*)

(* Epsilon *)
Theorem eps_exist: forall R A, exists E, wo R A ->
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

Definition eps (R: set) (A: set) := extract_set (eps_exist R A).
Definition eps_image (R: set) (A: set) := ran(eps R A).
Definition eps_rel (R: set) (A: set) := 
  subset_ctor (fun s => exists x y, s = ⟨x, y⟩ /\ x ∈ y) 
  (cp (eps_image R A) (eps_image R A)). 

Lemma eps_function: forall R A, wo R A -> function (eps R A).
Proof.
  intros R A P1.
  destruct (extract_set_property (eps_exist R A) P1) as [P3 [P4 P5]].
  apply P3.
Qed.

Lemma eps_dom: forall R A, wo R A -> dom(eps R A) = A.
Proof.
  intros R A P1.
  destruct (extract_set_property (eps_exist R A) P1) as [P3 [P4 P5]].
  apply P4.
Qed.

Lemma eps_elim_1: forall R A t, wo R A -> t ∈ A -> 
  (eps R A)[t] = (eps R A)[|seg R A t|].
Proof.
  intros R A t P1 P2.
  destruct (extract_set_property (eps_exist R A) P1) as [P3 [P4 P5]].
  apply (P5 _ P2).
Qed.

Lemma eps_elim_2: forall R A x s, wo R A -> x ∈ A -> s ∈ (eps R A)[x] ->
  exists y, s = (eps R A)[y] /\ y ∈ A /\ y <[R] x.
Proof.
  intros R A x s P1 P2 P3.
  rewrite (eps_elim_1 _ _ _ P1 P2) in P3.
  destruct (image_elim _ _ _ P3) as [y [P4 P5]].
  exists y.
  split.
  + apply (fval_intro).
    - apply (eps_function _ _ P1).
    - apply P4.
  + split.
    - apply (seg_elim_1 _ _ _ _ P2 P5).
    - apply (seg_elim_2 _ _ _ _ P2 P5).
Qed.

Lemma eps_less: forall R A x y, wo R A -> x ∈ A -> y ∈ A -> x <[R] y -> 
  (eps R A)[x] ∈ (eps R A)[y].
Proof.
  intros R A x y P1 P2 P3 P4.
  rewrite (eps_elim_1 _ _ _ P1 P3).
  apply image_intro.
  exists x.
  split.
  + apply fval_intro_2.
    apply (eps_function _ _ P1).
    rewrite (eps_dom _ _ P1).
    apply P2.
  + apply (seg_intro _ _ _ _ P2 P4).
Qed.

Lemma eps_asym: forall R A t, wo R A -> t ∈ A -> 
  (eps R A)[t] ∉  (eps R A)[t].
Proof.
  intros R A t P1 P2.
  pose (subset_ctor (fun x => (eps R A)[x] ∈ (eps R A)[x]) A) as S.
  destruct (LEM (S = ∅)) as [P3|P3].
  + apply (subset_empty _ _ _ P3 P2).
  + destruct (wo_least_elmn _ _ P1 _ (subset_elim_2 _ _) P3) as [x [Q1 Q2]].
    destruct (subset_elim _ _ _ Q1) as [Q3 Q4].
    assert (eps R A [x] ∈ eps R A [|seg R A x|]) as Q5.
    { rewrite <- (eps_elim_1 R A x P1 Q3).
      apply Q4. }
    destruct (image_elim _ _ _ Q5) as [y [Q6 Q7]].
    destruct (subset_elim _ _ _ Q7) as [Q8 Q9].
    absurd (y <[R] x).
    - apply (wo_le _ _ _ _ P1 Q3 Q8).
      apply Q2.
      apply (subset_intro _ _ _ Q8).
      rewrite <- (fval_intro _ _ _ (eps_function _ _ P1) Q6).
      apply Q4.
    - apply Q9.
Qed.

Lemma eps_injection: forall R A, wo R A -> injection (eps R A).
Proof.
  intros R A P1.
  split. 
  + apply (eps_function R A P1).
  + intros a1 a2 b P2 P3.
    assert (a1 ∈ A) as P4.
    { rewrite <- (eps_dom _ _ P1).
      apply (dom_intro_2 _ _ _ P2). }
    assert (a2 ∈ A) as P5.
    { rewrite <- (eps_dom _ _ P1).
      apply (dom_intro_2 _ _ _ P3). }
    destruct (wo_trichotomy_weak _ _ P1 _ _ P4 P5) as [P6|[P6|P6]].
    - pose (eps_less _ _ _ _ P1 P4 P5 P6) as Q1.
      rewrite <- (fval_intro _ _ _ (eps_function _ _ P1) P2) in Q1.
      rewrite (fval_intro _ _ _ (eps_function _ _ P1) P3) in Q1.
      pose (eps_asym _ _ _ P1 P5) as Q2.
      contradiction.
    - apply P6.
    - pose (eps_less _ _ _ _ P1 P5 P4 P6) as Q1.
      rewrite <- (fval_intro _ _ _ (eps_function _ _ P1) P2) in Q1.
      rewrite (fval_intro _ _ _ (eps_function _ _ P1) P3) in Q1.
      pose (eps_asym _ _ _ P1 P5) as Q2.
      contradiction.
Qed.

Lemma eps_fonto: forall R A, wo R A -> fonto (eps R A) A (eps_image R A).
Proof.
  intros R A P1.
  split.
  + apply (eps_function R A P1).
  + split.
    - apply (eps_dom R A P1).
    - reflexivity.
Qed.

Lemma eps_bijection: forall R A, wo R A -> 
  bijection (eps R A) A (eps_image R A).
Proof.
  intros R A P1.
  split.
  + apply (eps_injection _ _ P1).
  + apply (eps_fonto _ _ P1).
Qed.

Lemma eps_in: forall R A x y, wo R A -> x ∈ A -> y ∈ A -> 
  (eps R A)[x] ∈ (eps R A)[y] -> x <[R] y.
Proof.
  intros R A x y P1 P2 P3 P4.
  destruct (eps_elim_2 _ _ _ _ P1 P3 P4) as [s [P5 [P6 P7]]].
  rewrite <- (eps_dom _ _ P1) in P2. 
  rewrite <- (eps_dom _ _ P1) in P6. 
  rewrite (fval_injection _ _ _ (eps_injection _ _ P1) P2 P6 P5).
  apply P7.
Qed.

Lemma eps_image_intro_1: forall R A x, wo R A -> x ∈ A ->
  (eps R A)[x] ∈ (eps_image R A).
Proof.
  intros R A x P1 P2.
  apply ran_intro.
  exists x. 
  apply fval_elim.
  + reflexivity.
  + apply (eps_function _ _ P1).
  + rewrite (eps_dom _ _ P1).
    apply P2.
Qed.

Lemma eps_image_intro_2: forall R A x s, wo R A -> x ∈ A -> s ∈ (eps R A)[x] ->
  s ∈ (eps_image R A).
Proof.
  intros R A x s P1 P2 P3.
  destruct (eps_elim_2 _ _ _ _ P1 P2 P3) as [y [P4 [P5 P6]]].
  rewrite P4.
  apply (eps_image_intro_1 _ _ _ P1 P5).
Qed.

Lemma eps_image_elim: forall R A x, wo R A -> x ∈ (eps_image R A) -> 
  exists s, s ∈ A /\ x = (eps R A)[s].
Proof.
  intros R A x P1 P2.
  destruct (ran_elim _ _ P2) as [s P3].
  exists s.
  split.
  + rewrite <- (eps_dom _ _ P1).
    apply (dom_intro_2 _ _ _ P3).
  + apply (fval_intro _ _ _ (eps_function _ _ P1) P3).
Qed.

Lemma eps_image_trans: forall R A, wo R A -> trans (eps_image R A).
Proof.
  intros R A P1 x a P2 P3.
  destruct (eps_image_elim _ _ _ P1 P3) as [s [P4 P5]].
  rewrite P5 in P2.
  apply (eps_image_intro_2 _ _ _ _ P1 P4 P2).
Qed.

Lemma eps_rel_intro: forall R A a1 a2, wo R A -> a1 ∈ A -> a2 ∈ A -> 
  (eps R A)[a1] ∈ (eps R A)[a2] -> (eps R A)[a1] <[eps_rel R A] (eps R A)[a2].
Proof.
  intros R A a1 a2 P1 P2 P3 P4.
  apply subset_intro.
  + apply cp_intro.
    - apply (eps_image_intro_1 _ _ _ P1 P2).
    - apply (eps_image_intro_1 _ _ _ P1 P3).
  + exists ((eps R A)[a1]).
    exists ((eps R A)[a2]).
    split.
    - reflexivity.
    - apply P4.
Qed.
    
Lemma eps_rel_elim: forall R A a1 a2, wo R A -> a1 ∈ A -> a2 ∈ A -> 
  (eps R A)[a1] <[eps_rel R A] (eps R A)[a2] -> (eps R A)[a1] ∈ (eps R A)[a2].
Proof.
  intros R A a1 a2 P1 P2 P3 P4.
  destruct (subset_elim _ _ _ P4) as [_ [x [y [P5 P6]]]].
  rewrite (opair_equal_elim_fst _ _ _ _ P5).
  rewrite (opair_equal_elim_snd _ _ _ _ P5).
  apply P6.
Qed.
    
Lemma eps_less_rel: forall R A x y, wo R A -> x ∈ A -> y ∈ A -> x <[R] y -> 
  (eps R A)[x] <[eps_rel R A] (eps R A)[y].
Proof.
  intros R A x y P1 P2 P3 P4.
  apply (eps_rel_intro _ _ _ _ P1 P2 P3).
  apply (eps_less _ _ _ _ P1 P2 P3 P4).
Qed.

Lemma eps_in_rel: forall R A x y, wo R A -> x ∈ A -> y ∈ A -> 
  (eps R A)[x] <[eps_rel R A] (eps R A)[y] -> x <[R] y.
Proof.
  intros R A x y P1 P2 P3 P4.
  apply (eps_in _ _ _ _ P1 P2 P3).
  apply (eps_rel_elim _ _ _ _ P1 P2 P3 P4).
Qed.

Lemma eps_image_rel_eq: forall R A S B, wo R A -> wo S B -> 
  eps_image R A = eps_image S B -> eps_rel R A = eps_rel S B.
Proof.
  intros R A S B P1 P2 P3.
  unfold eps_rel.
  rewrite P3.
  reflexivity.
Qed.
(*----------------------------------------------------------------------------*)

(* Isomorphrism *)
Definition isom (R: set) (A: set) (S: set) (B: set) :=  
  exists f, bijection f A B /\ 
  (forall x y, x ∈ A -> y ∈ A -> ⟨x, y⟩ ∈ R -> ⟨f[x], f[y]⟩ ∈ S) /\
  (forall x y, x ∈ A -> y ∈ A -> ⟨f[x], f[y]⟩ ∈ S -> ⟨x, y⟩ ∈ R).

Lemma isom_refl: forall R A, isom R A R A.
Proof.
  intros R A.
  exists (id A).
  split.
  + apply id_is_bijection.
  + split.
    - intros x y P1 P2 P3.
      rewrite (id_fval _ _ P1).
      rewrite (id_fval _ _ P2).
      apply P3.
    - intros x y P1 P2 P3.
      rewrite <- (id_fval _ _ P1).
      rewrite <- (id_fval _ _ P2).
      apply P3.
Qed.

Lemma isom_sym: forall R A S B, isom R A S B -> isom S B R A.
Proof.
  intros R A S B [f [P1 [P2 P3]]].
  exists (inv f).
  split.
  + apply (inv_bijection _ _ _ P1).
  + split.
    - intros x y P4 P5 P6.
      apply P3.
      * destruct P1 as [[_ P7] [_ [P8 P9]]].
        rewrite <- P8.
        rewrite <- (inv_ran f).
        apply fval_ran.
        ++apply inv_function.
          apply P7.
        ++rewrite inv_dom.
          rewrite P9.
          apply P4.
      * destruct P1 as [[_ P7] [_ [P8 P9]]].
        rewrite <- P8.
        rewrite <- (inv_ran f).
        apply fval_ran.
        ++apply inv_function.
          apply P7.
        ++rewrite inv_dom.
          rewrite P9.
          apply P5.
      * destruct P1 as [P7 [_ [_ P8]]].
        rewrite <- P8 in P4.
        rewrite <- P8 in P5.
        rewrite (inv_function_exist_2 _ P7 _ P4).
        rewrite (inv_function_exist_2 _ P7 _ P5).
        apply P6.
    - intros x y P4 P5 P6.
      assert ((inv f)[x] ∈ A) as Q1.
      { destruct P1 as [P7 [_ [P8 P9]]].
        rewrite <- P8.
        rewrite <- inv_ran.
        apply ran_intro.
        exists x.
        apply fval_elim.
        + reflexivity.
        + apply inv_function.
          destruct P7 as [_ P7].
          apply P7.
        + rewrite inv_dom.
          rewrite P9. 
          apply P4. }
      assert ((inv f)[y] ∈ A) as Q2.
      { destruct P1 as [P7 [_ [P8 P9]]].
        rewrite <- P8.
        rewrite <- inv_ran.
        apply ran_intro.
        exists y.
        apply fval_elim.
        + reflexivity.
        + apply inv_function.
          destruct P7 as [_ P7].
          apply P7.
        + rewrite inv_dom.
          rewrite P9. 
          apply P5. }
      pose (P2 _ _ Q1 Q2 P6) as Q3.
      destruct P1 as [P7 [_ [_ P8]]].
      rewrite <- P8 in P4.
      rewrite <- P8 in P5.
      rewrite (inv_function_exist_2 _ P7 _ P4) in Q3.
      rewrite (inv_function_exist_2 _ P7 _ P5) in Q3.
      apply Q3.
Qed.

Lemma isom_trans: forall R A S B T C, isom R A S B -> isom S B T C -> 
  isom R A T C.
Proof.
  intros R A S B T C [f [P1 [P2 P3]]] [g [P4 [P5 P6]]].
  exists (g ∘ f).
  split.
  + apply (comp_bijection _ _ _ _ _ P1 P4).
  + split.
    - intros x y Q1 Q2 Q3.
      destruct P1 as [[P1 _] [_ [P7 P8]]].
      destruct P4 as [[P4 _] [_ [P9 _]]].
      assert (f[x] <[S] f[y]) as Q6.
      { apply (P2 _ _ Q1 Q2 Q3). }
      rewrite <- P7 in Q1.
      rewrite <- P7 in Q2.
      pose (fval_ran _ _ P1 Q1) as Q4.
      pose (fval_ran _ _ P1 Q2) as Q5.
      rewrite P8 in Q4.
      rewrite P8 in Q5.
      rewrite <- P9 in P8.
      rewrite <- (comp_coin_dom _ _ P8) in Q1.
      rewrite <- (comp_coin_dom _ _ P8) in Q2.
      rewrite <- (comp_elim_fval _ _ _ P1 P4 Q1).
      rewrite <- (comp_elim_fval _ _ _ P1 P4 Q2).
      apply (P5 _ _ Q4 Q5 Q6).
    - intros x y Q1 Q2 Q3.
      destruct P1 as [_ [P7 [P8 P9]]].
      destruct P4 as [_ [P10 [P11 _]]].
      apply (P3 _ _ Q1 Q2).
      apply P6.
      * rewrite <- P9.
        rewrite <- P8 in Q1.
        apply (fval_ran _ _ P7 Q1).
      * rewrite <- P9.
        rewrite <- P8 in Q2.
        apply (fval_ran _ _ P7 Q2).
      * rewrite <- P11 in P9.
        rewrite <- (comp_coin_dom _ _ P9) in P8.
        rewrite <- P8 in Q1.
        rewrite <- P8 in Q2.
        rewrite (comp_elim_fval _ _ _ P7 P10 Q1).
        rewrite (comp_elim_fval _ _ _ P7 P10 Q2).
        apply Q3.
Qed.
(* Skip 7F *)

Lemma isom_r_irrefl: forall R A S B, r_irrefl R A -> isom R A S B -> 
  r_irrefl S B.
Proof.
  intros R A S B P1 [f [P2 [P3 P4]]] x P5 P6.
  destruct P2 as [[Q1 Q2] [_ [Q3 Q4]]].
  assert ((inv f)[x] ∈ A) as P7.
  { rewrite <- Q3.
    rewrite <- (inv_ran f).
    apply (fval_ran).
    + apply inv_function.
      apply Q2.
    + rewrite (inv_dom f).
      rewrite Q4.
      apply P5. }
  rewrite <- Q4 in P5.
  rewrite <- (inv_function_exist_2 _ (conj Q1 Q2) _ P5) in P6.
  pose (P4 _ _ P7 P7 P6).
  pose (P1 _ P7).
  contradiction.
Qed.

Lemma isom_r_trans: forall R A S B, r_trans R A -> isom R A S B -> r_trans S B.
Proof.
  intros R A S B P1 P2 x y z Q1 Q2 Q3 P3 P4.
  destruct (isom_sym _ _ _ _ P2) as [f [P5 [P6 P7]]].
  pose (P6 _ _ Q1 Q2 P3) as P8.
  pose (P6 _ _ Q2 Q3 P4) as P9.
  destruct P5 as [_ P5].
  pose (P1 _ _ _ (fval_ran_fonto _ _ _ _ P5 Q1) (fval_ran_fonto _ _ _ _ P5 Q2)
    (fval_ran_fonto _ _ _ _ P5 Q3) P8 P9) as P10.
  apply (P7 _ _ Q1 Q3 P10).
Qed.

Lemma isom_trichotomy: forall R A S B, trichotomy R A -> isom R A S B -> 
  trichotomy S B.
Proof.
  intros R A S B P1 P2 x y Q1 Q2.
  destruct (isom_sym _ _ _ _ P2) as [f [[P8 P5] [P6 P7]]].
  destruct (P1 _ _ (fval_ran_fonto _ _ _ _ P5 Q1) 
    (fval_ran_fonto _ _ _ _ P5 Q2)) as 
    [[S1 [S2 S3]]|[[S1 [S2 S3]]|[S1 [S2 S3]]]].
  + left.
    repeat split.
    - apply (P7 _ _ Q1 Q2 S1).
    - intros P9.
      absurd (f[x] = f[y]).
      * apply S2.
      * rewrite P9.
        reflexivity.
    - intros P9.
      absurd (f[y] <[R] f[x]).
      * apply S3.
      * apply (P6 _ _ Q2 Q1 P9). 
  + right. left.
    repeat split.
    - intros P9.
      absurd (f[x] <[R] f[y]).
      * apply S1.
      * apply (P6 _ _ Q1 Q2 P9). 
    - destruct P8 as [P8 P9].
      destruct P5 as [_ [P10 P11]].
      apply (P9 _ _ (f[x])).
      * apply (fval_intro_2 _ _ P8).
        rewrite P10.
        apply Q1.
      * rewrite S2.
        apply (fval_intro_2 _ _ P8).
        rewrite P10.
        apply Q2.
    - intros P9.
      absurd (f[y] <[R] f[x]).
      * apply S3.
      * apply (P6 _ _ Q2 Q1 P9). 
  + right. right.
    repeat split.
    - intros P9.
      absurd (f[x] <[R] f[y]).
      * apply S1.
      * apply (P6 _ _ Q1 Q2 P9). 
    - intros P9.
      absurd (f[x] = f[y]).
      * apply S2.
      * rewrite P9.
        reflexivity.
    - apply (P7 _ _ Q2 Q1 S3).
Qed.

Lemma isom_least_elmn: forall R A S B, least_elmn R A -> isom R A S B -> 
  least_elmn S B.
Proof.
  intros R A S B P1 P2 C P3 P4.
  destruct P2 as [f [[P5 [P6 [P7 P8]]] [P9 P10]]].
  assert ((inv f)[|C|] ⊆ A) as Q1.
  { rewrite <- P7.
    apply (inv_image_ran). }
  assert ((inv f)[|C|] <> ∅) as Q2.
  { destruct (not_empty_exist_elmn _ P4) as [x P11].
    apply exist_elmn_not_empty.
    exists ((inv f)[x]).
    apply image_intro.
    exists x.
    split.
    + apply fval_intro_2.
      - apply inv_function.
        destruct P5 as [_ P5].
        apply P5.
      - rewrite (inv_dom f).
        rewrite P8.
        apply (P3 _ P11).
    + apply P11. }
  destruct (P1 _ Q1 Q2) as [x [Q3 Q4]].
  exists (f[x]).
  split.
  + destruct (image_elim _ _ _ Q3) as [y [Q5 Q6]].
    rewrite <- (fval_intro _ _ _ P6 (inv_elim _ _ _ Q5)).
    apply Q6.
  + intros y P11.
    assert ((inv f)[y] ∈ (inv f)[|C|]) as P12.
    { apply image_intro_2.
      + apply (inv_function).
        destruct P5 as [_ P5].
        apply P5.
      + rewrite (inv_dom f).
        rewrite P8.
        apply (P3 _ P11).
      + apply P11. }
    destruct (Q4 _ P12) as [Q5|Q5].
    - left.
      pose (P3 _ P11) as Q6.
      rewrite <- P8 in Q6.
      rewrite <- (inv_function_exist_2 _ P5 _ Q6).
      apply P9.
      * rewrite <- P7.
        destruct (image_elim _ _ _ Q3) as [s [Q7 _]].
        apply (dom_intro_2 _ _ _ (inv_elim _ _ _ Q7)).
      * rewrite <- P7.
        rewrite <- (inv_ran f).
        apply fval_ran. 
        ++apply (inv_function).
          destruct P5 as [_ P5].
          apply P5.
        ++rewrite (inv_dom f).
          apply Q6.
      * apply Q5.
    - right.
      rewrite Q5.
      pose (P3 _ P11) as Q6.
      rewrite <- P8 in Q6.
      apply (inv_function_exist_2 _ P5 _ Q6).
Qed.

Lemma isom_po: forall R A S B, po R A -> isom R A S B -> po S B.
Proof.
  intros R A S B [P1 P2] P3.
  split.
  + apply (isom_r_trans _ _ _ _ P1 P3).
  + apply (isom_r_irrefl _ _ _ _ P2 P3).
Qed.

Lemma isom_lo: forall R A S B, lo R A -> isom R A S B -> lo S B.
Proof.
  intros R A S B [P1 P2] P3.
  split.
  + apply (isom_r_trans _ _ _ _ P1 P3).
  + apply (isom_trichotomy _ _ _ _ P2 P3).
Qed.

Lemma isom_wo: forall R A S B, wo R A -> isom R A S B -> wo S B.
Proof.
  intros R A S B [P1 P2] P3.
  split.
  + apply (isom_lo _ _ _ _ P1 P3).
  + apply (isom_least_elmn _ _ _ _ P2 P3).
Qed.

Lemma isom_wo_eps: forall R A, wo R A -> isom R A (eps_rel R A) (eps_image R A).
Proof.
  intros R A P1.
  exists (eps R A).
  split.
  + apply (eps_bijection _ _ P1).
  + split.
    - intros x y P2 P3 P4.
      apply (eps_less_rel _ _ _ _ P1 P2 P3 P4).
    - intros x y P2 P3 P4.
      apply (eps_in_rel _ _ _ _ P1 P2 P3 P4).
Qed.
(*----------------------------------------------------------------------------*)
  
(* Ordinal *)
Lemma wo_eps_eq_isom: forall R A S B, wo R A -> wo S B -> 
  eps_image R A = eps_image S B -> isom R A S B.
Proof.
  intros R A S B P1 P2 P3.
  pose (isom_wo_eps _ _ P1) as Q1.
  pose (isom_sym _ _ _ _ (isom_wo_eps _ _ P2)) as Q2.
  rewrite P3 in Q1.
  rewrite (eps_image_rel_eq _ _ _ _ P1 P2 P3) in Q1.
  apply (isom_trans _ _ _ _ _ _ Q1 Q2).
Qed.

Lemma wo_isom_eps_eq: forall R1 A1 R2 A2, wo R1 A1 -> wo R2 A2 -> 
  isom R1 A1 R2 A2 -> eps_image R1 A1 = eps_image R2 A2.
Proof.
  intros R1 A1 R2 A2 P1 P2 [f [P3 [P4 P5]]].
  pose (subset_ctor (fun x => (eps R1 A1)[x] = (eps R2 A2)[f[x]]) A1) as B.
  assert (B ⊆ A1) as I1.
  { intros x Q1. 
    destruct (subset_elim _ _ _ Q1) as [Q2 _].
    apply Q2. }
  assert (forall s, s ∈ A1 -> seg R1 A1 s ⊆ B -> s ∈ B) as I2.
  { intros s Q1 Q2.
    apply subset_intro.
    + apply Q1.
    + apply subset_asym.
      destruct P3 as [P6 [P3 [P7 P8]]].
      split.
      - intros x Q3.
        destruct (eps_elim_2 _ _ _ _ P1 Q1 Q3) as [s0 [Q4 [Q5 Q6]]].
        destruct (subset_elim _ _ _ (Q2 _ (seg_intro _ _ _ _ Q5 Q6))) as [_ Q7].
        rewrite Q4.
        rewrite Q7.
        apply (eps_less _ _ _ _ P2).
        * rewrite <- P8.
          apply (fval_ran _ _ P3).
          rewrite P7.
          apply Q5.
        * rewrite <- P8.
          apply (fval_ran _ _ P3).
          rewrite P7.
          apply Q1.
        * apply (P4 _ _ Q5 Q1 Q6).
      - intros x Q3.
        assert (f[s] ∈ A2) as Q4.
        { rewrite <- P8. 
          apply (fval_ran _ _ P3).
          rewrite P7.
          apply Q1. }
        destruct (eps_elim_2 _ _ _ _ P2 Q4 Q3) as [s0 [Q5 [Q6 Q7]]].
        rewrite <- P8 in Q6.
        rewrite <- (inv_function_exist_2 _ P6 _ Q6) in Q7.
        rewrite <- (inv_function_exist_2 _ P6 _ Q6) in Q5.
        assert ((inv f)[s0] ∈ A1) as Q8.
        { rewrite <- P7.
          rewrite <- (inv_ran f).
          apply fval_ran.
          + destruct P6 as [_ P6].
            apply inv_function.
            apply P6.
          + rewrite (inv_dom f).
            apply Q6. }
        pose (P5 _ _ Q8 Q1 Q7) as Q9.
        rewrite P8 in Q6.
        destruct (subset_elim _ _ _ (Q2 _ (seg_intro _ _ _ _ Q8 Q9))) 
          as [_ Q10].
        rewrite Q5.
        rewrite <- Q10.
        apply (eps_less _ _ _ _ P1).
        * apply Q8.
        * apply Q1.
        * apply Q9. }
  pose (transfinite_induction _ _ _ P1 (conj I1 I2)) as I3.
  apply subset_asym.
  split.
  + intros x Q1.
    destruct (eps_image_elim _ _ _ P1 Q1) as [s [Q2 Q3]].
    rewrite Q3.
    rewrite I3 in Q2.
    destruct (subset_elim _ _ _ Q2) as [_ Q4].
    rewrite Q4.
    apply (eps_image_intro_1 _ _ _ P2).
    destruct P3 as [_ [P3 [P6 P7]]].
    rewrite <- P7.
    apply (fval_ran _ _ P3).
    rewrite P6.
    apply (I1 _ Q2).
  + intros x Q1.
    destruct (eps_image_elim _ _ _ P2 Q1) as [s [Q2 Q3]].
    assert ((inv f)[s] ∈ A1) as Q4.
    { destruct P3 as [[P3 P6] [_ [P7 P8]]].
      rewrite <- P7.
      rewrite <- (inv_ran f).
      apply fval_ran.
      * apply inv_function.
        apply P6.
      * rewrite (inv_dom f).
        rewrite P8.
        apply Q2. }
    destruct P3 as [P3 [_ [_ P6]]].
    rewrite <- P6 in Q2.
    rewrite <- (inv_function_exist_2 _ P3 _ Q2) in Q3.
    rewrite I3 in Q4.
    destruct (subset_elim _ _ _ Q4) as [_ Q5].
    rewrite Q3.
    rewrite <- Q5.
    apply (eps_image_intro_1 _ _ _ P1).
    apply (I1 _ Q4).
Qed.

Definition ord (x: set) := exists R A, wo R A /\ x = (eps_image R A).

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

Lemma wo_seg: forall R A x, wo R A -> x ∈ A -> wo R (seg R A x).
Proof.
  intros R A x P1 P2.
  apply (wo_subset _ _ _ P1).
  apply (subset_elim_2).
Qed.

(*Lemma eps_image_seg_1: forall R A s, wo R A -> s ∈ A -> *)
  (*eps R A [|seg R A s|] = eps_image R (seg R A s).*)
(*Proof.*)
  (*intros R A s P1 P2.*)
  (*apply subset_asym.*)
  (*split.*)
  (*+ intros x P3.*)
    (*destruct (image_elim _ _ _ P3) as [s0 [P4 P5]].*)
    (*pose (seg_elim_1 _ _ _ _ P2 P5) as P6.*)
    (*pose (eps_image_intro_2). _ _ _ _ (wo_seg _ _ _ P1 P6)). *)
    (*apply (eps_image_intro_2 _ _ _ _ (wo_seg _ _ _ P1 P6)). *)
      (*(seg_elim_1 _ _ _ _ P2 P5)).*)
  (*pose (eps_elim_1 ).*)

(*Lemma eps_image_seg: forall R A s, wo R A -> s ∈ A -> *)
  (*(eps R A)[s] = eps_image R (seg R A s).*)
(*Proof.*)
  (*intros R A s P1 P2.*)
  (*pose eps_elim_1.*)
  (*apply subset_asym.*)
  (*split.*)
  (*apply (eps_elim_1).*)
  (*+ intros x P3.*)
    
(*Lemma ord_trans_class: forall x y, ord x -> y ∈ x -> ord y.*)
(*Proof.*)
  (*intros x y [R [A [P1 P2]]] P3.*)
  (*rewrite P2 in P3.*)
  (*destruct (eps_image_elim _ _ _ P1 P3) as [s [P4 P5]].*)
  (*exists R.*)
  (*exists (seg R A s).*)
  (*split.*)
  (*+ apply (wo_seg _ _ _ P1 P4).*)
  (*+ pose (eps_image_intro).*)
  
(*Lemma wo_isom_trichotomy: forall R A S B, wo R A -> wo S B -> *)
  (*isom R A S B \/ exists b, b ∈ B /\ isom R A (seg b*)

