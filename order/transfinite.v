Require Import axiom.axiom.
Require Import axiom.logic.
Require Import operation.basic.
Require Import relation.relation.
Require Import relation.function.
Require Import relation.util_function.
Require Import relation.equiv.
Require Import nat.inductive.
Require Import nat.nat.
Require Import order.order.
 
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
  
