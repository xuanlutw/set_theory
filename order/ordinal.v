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
Require Import order.isom.

(* Ordinal *)
Lemma wo_seg: forall R A x, wo R A -> x ∈ A -> wo R (seg R A x).
Proof.
  intros R A x P1 P2.
  apply (wo_subset _ _ _ P1).
  apply (subset_elim_2).
Qed.

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

Lemma ord_intro: forall R A, wo R A -> exists x, ord x.
Proof.
  intros R A P1.
  exists (eps_image R A).
  exists R.
  exists A.
  split.
  + apply P1.
  + reflexivity.
Qed.

(*Lemma eps_image_seg: forall R A s, wo R A -> s ∈ A -> *)
  (*(eps R A)[s] = eps_image R (seg R A s).*)
(*Proof.*)
  (*intros R A s P1 P2.*)
  (*apply subset_asym.*)
  (*split.*)
  (*+ intros x P3.*)
    (*apply (eps_image_intro_2 _ _ x).*)
    (*- apply (wo_seg _ _ _ P1 P2).*)
    (*- pose seg_intro.*)
  (*pose eps_elim_1.*)
  (*apply (eps_elim_1).*)
  (*+ intros x P3.*)
    
(*Lemma ord_trans: forall x y, ord x -> y ∈ x -> ord y.*)
(*Proof.*)
  (*intros x y [R [A [P1 P2]]] P3.*)
  (*rewrite P2 in P3.*)
  (*destruct (eps_image_elim _ _ _ P1 P3) as [s [P4 P5]].*)
  (*exists R.*)
  (*exists (seg R A s).*)
  (*split.*)
  (*+ apply (wo_seg _ _ _ P1 P4).*)
  (*+ rewrite P5.*)
    (*pose (eps_image_intro).*)
  
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

(*Lemma wo_isom_trichotomy: forall R A S B, wo R A -> wo S B -> *)
  (*isom R A S B \/ exists b, b ∈ B /\ isom R A (seg b*)
