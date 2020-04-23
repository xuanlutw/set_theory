Require Import axiom.logic.
Require Import axiom.axiom.
Require Import operation.basic.
Require Import relation.relation.
Require Import relation.function.
Require Import relation.util_function.
Require Import relation.equiv.
Require Import nat.inductive.
Require Import nat.nat.
Require Import order.order.
Require Import order.transfinite.

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
