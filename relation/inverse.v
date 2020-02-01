Require Import axiom.logic.
Require Import axiom.axiom.
Require Import axiom.ax_choice.
Require Import operation.basic.
Require Import relation.relation.
Require Import relation.function.
Require Import relation.util_function.

(* Inverse Function *)
(* 3J *)
Lemma left_inverse: forall F A B, A <> ∅ -> fover F A B -> 
  ((exists G, fover G B A /\ (id A = (G ∘ F))) <-> injection F).
Proof.
  intros F A B P1 [P2 [P3 P4]].
  split.
  + intros [G [[[_ P5] _] P6]].
    split.
    - apply P2.
    - intros a1 a2 b P7 P8.
      pose (dom_intro_2 _ _ _ P7) as P11.
      rewrite P3 in P11.
      pose (id_intro _ _ P11) as P12.
      rewrite P6 in P12.
      destruct (comp_elim _ _ _ _ P12) as [y1 [P13 P14]].
      pose (dom_intro_2 _ _ _ P8) as P21.
      rewrite P3 in P21.
      pose (id_intro _ _ P21) as P22.
      rewrite P6 in P22.
      destruct (comp_elim _ _ _ _ P22) as [y2 [P23 P24]].
      destruct P2 as [_ P2].
      rewrite <- (P2 _ _ _ P7 P13) in P14.
      rewrite <- (P2 _ _ _ P8 P23) in P24.
      apply (P5 _ _ _ P14 P24).
  + intros [P5 P6].
    destruct (not_empty_exist_elmn _ P1) as [a P7]. 
    exists ((inv F) ∪ (const (B \ ran(F)) a)).
    split. split.
    - apply piecewise_function. 
      * apply inv_function. 
        apply P6.
      * apply const_is_function.
      * rewrite <- const_dom.
        rewrite inv_dom.
        apply complement_inter2.
    - split.
      * rewrite (union2_dom).
        rewrite inv_dom.
        rewrite <- const_dom.
        rewrite complement_union2.
        apply (union2_subset_absorb_l _ _ P4).
      * rewrite (union2_ran).
        rewrite inv_ran.
        destruct (LEM (B \ (ran(F)) = ∅)) as [P8|P8].
        { assert (ran(const (B \ (ran( F))) a) = ∅) as P9.
          { apply (empty_dom_empty_ran _ (const_is_function _ _)).
            rewrite <- const_dom.
            apply P8. }
          rewrite P9.
          rewrite P3.
          rewrite union2_empty_absorb_r.
          apply subset_refl. }
        { rewrite <- (const_ran _ _ P8).
          rewrite P3.
          intros x P9.
          destruct (in_union2_in _ _ _ P9) as [P10|P10].
          + apply P10.
          + rewrite <- (in_singleton_equal _ _ P10).
            apply P7. }
    - apply subset_asym.
      split.
      * intros x P8.
        destruct (id_elim _ _ P8) as [s [P9 P10]].
        rewrite <- P3 in P9.
        rewrite P10.
        apply comp_intro.
        exists (F[s]).
        split.
        { apply (fval_intro_2 _ _ P2 P9). }
        { apply in_in_union2_1. 
          apply inv_intro.
          apply (fval_intro_2 _ _ P2 P9). }
      * intros x P8.
        destruct (comp_elim_2 _ _ _ P8) as [s [t [r [P9 [P10 P11]]]]].
        destruct (in_union2_in _ _ _ P11) as [P12|P12].
        { pose (inv_elim _ _ _ P12) as P13.
          rewrite (P6 _ _ _ P10 P13) in P9.
          rewrite (P6 _ _ _ P10 P13) in P10.
          rewrite P9.
          apply id_intro.
          rewrite <- P3.
          apply (dom_intro_2 _ _ _ P10). }
        { absurd (t ∈ ran(F)). 
          + pose (dom_intro_2 _ _ _ P12) as P13.
            rewrite <- const_dom in P13.
            destruct (complement_elim _ _ _ P13) as [_ P14].
            apply P14.
          + apply (ran_intro_2 _ _ _ P10). }
Qed.

Lemma right_inverse: forall F A B, A <> ∅ -> fover F A B -> 
  ((exists H, fover H B A /\ (id B = (F ∘ H))) <-> fonto F A B).
Proof.
  intros F A B P1 [P2 [P3 P4]].
  split.
  + intros [H [[[_ P5] _] P6]].
    split.
    - apply P2. 
    - split.
      * apply P3. 
      * apply subset_asym.
        split. 
        { apply P4. }
        { intros x P7.
          pose (id_intro _ _ P7) as P8.
          rewrite P6 in P8.
          destruct (comp_elim _ _ _ _ P8) as [y [_ P9]].
          apply (ran_intro_2 _ _ _ P9). }
  + intros [_ [_ P7]].
    destruct (ax_choice (inv F) (inv_is_rel F)) as [H [P8 [P9 P10]]].
    exists H.
    split. split.
    - apply P8.
    - split. 
      * rewrite P10.
        rewrite inv_dom.
        apply P7.
      * rewrite <- P3.
        rewrite <- (inv_ran F).
        apply (subset_ran _ _ P9).
    - apply subset_asym.
      split.
      * intros x P11.
        destruct (id_elim _ _ P11) as [b [P12 P13]].
        rewrite <- P7 in P12.
        rewrite <- inv_dom in P12.
        rewrite <- P10 in P12.
        rewrite P13.
        apply comp_intro.
        exists (H[b]).
        split.
        { apply (fval_intro_2 _ _ P8 P12). }
        { apply (inv_elim).
          apply P9.
          apply (fval_intro_2 _ _ P8 P12). }
      * intros x P11.
        destruct (comp_elim_2 _ _ _ P11) as [a [b [c [P12 [P13 P14]]]]].
        destruct P2 as [_ P2].
        rewrite (P2 _ _ _ P14 (inv_elim _ _ _ (P9 _ P13))) in P12.
        rewrite P12.
        apply id_intro.
        rewrite <- P7.
        rewrite <- inv_dom.
        rewrite <- P10.
        apply (dom_intro_2 _ _ _ P13).
Qed.
(*----------------------------------------------------------------------------*)
