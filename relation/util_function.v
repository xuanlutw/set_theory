Require Import axiom.logic.
Require Import axiom.axiom.
Require Import operation.basic.
Require Import relation.relation.
Require Import relation.function.

(* Empty Function *)
Lemma empty_is_rel: rel ∅.
Proof.
  intros x P1.
  absurd (x ∈ ∅).
  + apply not_in_empty.
  + apply P1.
Qed.

Lemma empty_is_single_value: single_value ∅.
Proof.
  intros a b1 b2 P1 P2.
  absurd (⟨a, b1⟩ ∈ ∅).
  + apply not_in_empty.
  + apply P1.
Qed.

Lemma empty_is_single_rooted: single_rooted ∅.
Proof.
  intros a1 a2 b P1 P2.
  absurd (⟨a1, b⟩ ∈ ∅).
  + apply not_in_empty.
  + apply P1.
Qed.

Lemma empty_is_function: function ∅.
Proof.
  split.
  + apply empty_is_rel.
  + apply empty_is_single_value.
Qed.

Lemma empty_is_injection: injection ∅.
Proof.
  split.
  + apply empty_is_function.
  + apply empty_is_single_rooted.
Qed.

Lemma empty_dom: dom(∅) = ∅.
Proof.
  apply subset_asym.
  split.
  + intros x P1.
    destruct (dom_elim _ _ P1) as [y P2].
    absurd (⟨x, y⟩ ∈ ∅).
    - apply not_in_empty.
    - apply P2.
  + intros x P1.
    absurd (x ∈ ∅).
    - apply not_in_empty.
    - apply P1.
Qed.

Lemma empty_ran: ran(∅) = ∅.
Proof.
  apply subset_asym.
  split.
  + intros y P1.
    destruct (ran_elim _ _ P1) as [x P2].
    absurd (⟨x, y⟩ ∈ ∅).
    - apply not_in_empty.
    - apply P2.
  + intros y P1.
    absurd (y ∈ ∅).
    - apply not_in_empty.
    - apply P1.
Qed.

Lemma fspace_empty_dom: forall B, fspace ∅ B = {∅}.
Proof.
  intros B.
  apply subset_asym.
  split.
  + intros x P1.
    assert (x = ∅) as P2.
    { apply empty_unique.
      intros s P2.
      destruct (fspace_elim _ _ _ P1) as [[P3 _] [P4 _]].
      destruct (P3 _ P2) as [p [q P5]].
      rewrite P5 in P2.
      absurd (dom(x) = ∅).
      + apply exist_elmn_not_empty.
        exists p.
        apply (dom_intro_2 _ _ _ P2).
      + apply P4. }
    rewrite P2.
    apply in_singleton.
  + intros x P1.
    apply fspace_intro.
    rewrite <- (in_singleton_equal _ _ P1).
    split.
    - apply empty_is_function.
    - split.
      * apply empty_dom.
      * rewrite empty_ran.
        apply empty_subset.
Qed.

Lemma fspace_empty_ran: forall A, A <> ∅ -> fspace A ∅ = ∅.
Proof.
  intros A P1.
  apply subset_asym.
  split.
  + intros x P2.
    destruct (fspace_elim _ _ _ P2) as [_ [P3 P4]].
    destruct (not_empty_exist_elmn _ P1) as [a P5].
    rewrite <- P3 in P5.
    destruct (dom_elim _ _ P5) as [b P7].
    absurd (b ∈ ∅).
    - apply not_in_empty.
    - apply (P4 _ (ran_intro_2 _ _ _ P7)).
  + intros x P2.
    absurd (x ∈ ∅).
    - apply not_in_empty.
    - apply P2.
Qed.

Lemma empty_dom_empty_ran: forall F, function F -> dom(F) = ∅ -> ran(F) = ∅.
Proof. 
  intros F P1 P2.
  pose (fonto_intro _ P1) as P3.
  rewrite P2 in P3.
  pose (fspace_intro _ _ _ (fonto_fover _ _ _ P3)) as P4.
  rewrite fspace_empty_dom in P4.
  rewrite <- (in_singleton_equal _ _ P4).
  apply empty_ran.
Qed.
(*----------------------------------------------------------------------------*)

(* Single Pair Function *)
Lemma single_pair_is_function: forall x y, function ({⟨x, y⟩}).
Proof.
  intros x y.
  split.
  + intros s P1.
    exists x.
    exists y.
    symmetry.
    apply (in_singleton_equal _ _ P1).
  + intros a0 b1 b2 P1 P2.
    destruct (opair_equal_elim _ _ _ _ (in_singleton_equal _ _ P1)) as [_ P3].
    rewrite <- P3.
    destruct (opair_equal_elim _ _ _ _ (in_singleton_equal _ _ P2)) as [_ P4].
    apply P4.
Qed.

Lemma single_pair_dom: forall x y, dom({⟨x, y⟩}) = ({x}).
Proof. 
  intros x y.
  apply ax_exten.
  intros s.
  split.
  + intros P1.
    destruct (dom_elim _ _ P1) as [t P2].
    rewrite (opair_equal_elim_fst _ _ _ _ (in_singleton_equal _ _ P2)).
    apply in_singleton.
  + intros P1.
    apply dom_intro.
    exists y.
    rewrite (in_singleton_equal _ _ P1).
    apply in_singleton.
Qed.

Lemma single_pair_ran: forall x y, ran({⟨x, y⟩}) = ({y}).
Proof. 
  intros x y.
  apply ax_exten.
  intros s.
  split.
  + intros P1.
    destruct (ran_elim _ _ P1) as [t P2].
    rewrite <- (opair_equal_elim_snd _ _ _ _ (in_singleton_equal _ _ P2)).
    apply in_singleton.
  + intros P1.
    apply ran_intro.
    exists x.
    rewrite (in_singleton_equal _ _ P1).
    apply in_singleton.
Qed.
(*----------------------------------------------------------------------------*)

(* Identify Function *)
Definition id (A: set) :=
  (subset_ctor 
    (fun s => exists x, s = ⟨x, x⟩)
    (cp A A)).

Lemma id_intro: forall A x, x ∈ A -> ⟨x, x⟩ ∈ id A.
Proof.
  intros A x P1.
  destruct (extract_set_property (ax_subset 
    (fun s => exists x, s = ⟨x, x⟩)
    (cp A A)) (⟨x, x⟩)) as [_ P2].
  apply P2.
  split.
  + apply (cp_intro _ _ _ _ P1 P1).
  + exists x.
    reflexivity.
Qed.

Lemma id_elim: forall A s, s ∈ id A -> exists x, x ∈ A /\ s = ⟨x, x⟩.
Proof. 
  intros A s P1.
  destruct (extract_set_property (ax_subset 
    (fun s => exists x, s = ⟨x, x⟩)
    (cp A A)) s) as [P2 _].
  destruct (P2 P1) as [P3 [x P4]].
  destruct (cp_elim _ _ _ P3) as [a [b [P5 [_ P6]]]].
  exists x.
  split.
  + rewrite P4 in P6. 
    destruct (opair_equal_elim _ _ _ _ P6) as [P7 _].
    rewrite P7.
    apply P5.
  + apply P4.
Qed.

Lemma id_is_rel: forall A, rel (id A).
Proof.
  intros A x P1.
  destruct (id_elim _ _ P1) as [s [_ P2]].
  exists s.
  exists s.
  apply P2.
Qed.

Lemma id_is_single_value: forall A, single_value (id A).
Proof.
  intros A a b1 b2 P1 P2.
  destruct (id_elim _ _ P1) as [s1 [_ P3]].
  destruct (id_elim _ _ P2) as [s2 [_ P4]].
  rewrite (opair_equal_elim_snd _ _ _ _ P3).
  rewrite <- (opair_equal_elim_fst _ _ _ _ P3).
  rewrite (opair_equal_elim_snd _ _ _ _ P4).
  apply (opair_equal_elim_fst _ _ _ _ P4).
Qed.

Lemma id_is_single_rooted: forall A, single_rooted (id A).
Proof.
  intros A a1 a2 b P1 P2.
  destruct (id_elim _ _ P1) as [s1 [_ P3]].
  destruct (id_elim _ _ P2) as [s2 [_ P4]].
  rewrite (opair_equal_elim_fst _ _ _ _ P3).
  rewrite <- (opair_equal_elim_snd _ _ _ _ P3).
  rewrite (opair_equal_elim_fst _ _ _ _ P4).
  apply (opair_equal_elim_snd _ _ _ _ P4).
Qed.

Lemma id_is_function: forall A, function (id A).
Proof.
  intros A.
  split.
  + apply id_is_rel.
  + apply id_is_single_value.
Qed.

Lemma id_is_injection: forall A, injection (id A).
Proof.
  intros A.
  split.
  + apply id_is_function.
  + apply id_is_single_rooted.
Qed.

Lemma id_dom: forall A, A = dom(id A).
Proof.
  intros A.
  apply ax_exten.
  intros x.
  split.
  + intros P1. 
    apply (dom_intro_2 _ _ _ (id_intro A x P1)).
  + intros P1.
    destruct (dom_elim _ _ P1) as [y P2].
    destruct (id_elim _ _ P2) as [s [P3 P4]].
    rewrite (opair_equal_elim_fst _ _ _ _ P4).
    apply P3.
Qed.

Lemma id_ran: forall A, A = ran(id A).
Proof.
  intros A.
  apply ax_exten.
  intros y.
  split.
  + intros P1.
    apply (ran_intro_2 _ _ _ (id_intro A y P1)).
  + intros P1.
    destruct (ran_elim _ _ P1) as [x P2].
    destruct (id_elim _ _ P2) as [s [P3 P4]].
    rewrite (opair_equal_elim_snd _ _ _ _ P4).
    apply P3.
Qed.

Lemma id_fval: forall A x, x ∈ A -> (id A)[x] = x.
Proof.
  intros A x P1.
  symmetry.
  apply fval_intro.
  + apply (id_is_function A).
  + apply (id_intro _ _ P1).
Qed.

Lemma id_fonto: forall A, fonto (id A) A A.
Proof.
  intros A.
  split.
  + apply id_is_function.
  + split.
    - symmetry. 
      apply id_dom.
    - symmetry.
      apply id_ran.
Qed.

Lemma id_inv: forall A, id A = inv (id A).
Proof.
  intros A.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (id_elim _ _ P1) as [y [_ P2]].
    rewrite P2.
    apply inv_intro.
    rewrite <- P2.
    apply P1.
  + intro P1.
    destruct (inv_is_rel (id A) x P1) as [a [b P2]].
    rewrite P2 in P1.
    destruct (id_elim _ _ (inv_elim _ _ _ P1)) as [z [P3 P4]].
    rewrite P2.
    destruct (opair_equal_elim _ _ _ _ P4) as [P5 P6].
    rewrite P5.
    rewrite P6.
    apply (id_intro _ _ P3).
Qed.
(*----------------------------------------------------------------------------*)
    
(* Constant Function *)
Definition const (A: set) (c: set) :=
  cp A ({c}).

Lemma const_intro: forall A c x, x ∈ A -> ⟨x, c⟩ ∈ const A c.
Proof.
  intros A c x P1.
  apply cp_intro.
  + apply P1.
  + apply in_singleton.
Qed.

Lemma const_elim: forall A c s, s ∈ const A c -> 
  exists x, x ∈ A /\ s = ⟨x, c⟩.
Proof.
  intros A c s P1.
  destruct (cp_elim _ _ _ P1) as [a [b [P2 [P3 P4]]]].
  exists a.
  split.
  + apply P2.
  + rewrite (in_singleton_equal _ _ P3).
    apply P4.
Qed.

Lemma const_is_rel: forall A c, rel (const A c).
Proof.
  intros A c x P1.
  destruct (const_elim _ _ _ P1) as [a [_ P2]].
  exists a.
  exists c.
  apply P2.
Qed.

Lemma const_is_single_value: forall A c, single_value (const A c).
Proof. 
  intros A c a b1 b2 P1 P2.
  destruct (const_elim _ _ _ P1) as [a1 [_ P3]].
  rewrite (opair_equal_elim_snd _ _ _ _ P3).
  destruct (const_elim _ _ _ P2) as [a2 [_ P4]].
  symmetry.
  apply (opair_equal_elim_snd _ _ _ _ P4).
Qed.

Lemma const_is_function: forall A c, function (const A c).
Proof.
  intros A c.
  split.
  + apply const_is_rel. 
  + apply const_is_single_value. 
Qed.

Lemma const_dom: forall A c, A = dom(const A c).
Proof.
  intros A c.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    apply dom_intro.
    exists c.
    apply (const_intro _ _ _ P1).
  + intros P1.
    destruct (dom_elim _ _ P1) as [a P2].
    destruct (const_elim _ _ _ P2) as [b [P3 P4]].
    rewrite (opair_equal_elim_fst _ _ _ _ P4).
    apply P3.
Qed.

Lemma const_ran: forall A c, A <> ∅ -> {c} = ran(const A c).
  intros A c P1.
  apply ax_exten.
  intros x.
  split.
  + intros P2.
    apply ran_intro.
    destruct (not_empty_exist_elmn _ P1) as [a P3].
    exists a.
    rewrite (in_singleton_equal _ _ P2).
    apply (const_intro _ _ _ P3).
  + intros P2.
    destruct (ran_elim _ _ P2) as [a P3].
    destruct (const_elim _ _ _ P3) as [b [_ P4]].
    destruct (opair_equal_elim _ _ _ _ P4) as [_ P5].
    rewrite P5.
    apply in_singleton.
Qed.

Lemma const_fval: forall A c x, x ∈ A -> c = (const A c)[x].
Proof. 
  intros A c x P1.
  apply fval_intro.
  + apply const_is_function.
  + apply (const_intro _ _ _ P1).
Qed.
(*----------------------------------------------------------------------------*)
