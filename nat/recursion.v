Require Import axiom.axiom.
Require Import axiom.logic.
Require Import operation.basic.
Require Import relation.relation.
Require Import relation.function.
Require Import relation.util_function.
Require Import nat.inductive.
Require Import nat.nat.

(* Recursion Theorem *)
(* Need Rewrite *)
Definition _rec_accept (F: set) (A: set) (a: set) := fun f => 
    function f /\ dom(f) ⊆ ω /\ ran(f) ⊆ A /\ ∅ ∈ dom(f) /\ f[∅] = a /\ 
    (forall n, n ∈ ω-> S(n) ∈ dom(f) -> 
      n ∈ dom(f) /\ f[S(n)] = F[f[n]]).

Lemma _rec_fun: forall A a F, function (∪(subset_ctor (_rec_accept F A a) (𝒫(cp ω A)))).
Proof.
  intros A a F.
  pose (H := subset_ctor (_rec_accept F A a) (𝒫(cp ω A))).
  pose (h := ∪(H)).
  split.
  + apply union_rel.
    intros f P1.
    destruct (subset_elim _ _ _ P1) as [_ [[P2 _] _]].
    apply P2.
  + intros a0. 
    pose (PI := fun x => forall b1 b2, ⟨x, b1⟩ ∈ h -> ⟨x, b2⟩ ∈ h -> b1 = b2).
    assert (PI ∅) as P1.
    { intros b1 b2 P2 P3.
      destruct (in_union_in _ _ P2) as [H1 [Q1 Q2]].
      destruct (subset_elim _ _ _ Q1) as [_ [Q3 [_ [_ [Q4 [Q5 _]]]]]].
      symmetry in Q5.
      destruct (fval_elim _ _ _ Q5 Q3 Q4) as [_ Q6].
      rewrite <- (Q6 _ Q2).
      destruct (in_union_in _ _ P3) as [H2 [R1 R2]].
      destruct (subset_elim _ _ _ R1) as [_ [R3 [_ [_ [R4 [R5 _]]]]]].
      symmetry in R5.
      destruct (fval_elim _ _ _ R5 R3 R4) as [_ R6].
      apply (R6 _ R2). }
    assert (induction_step PI) as P2. 
    { intros k P2 P3 b1 b2 P4 P5.
      destruct (in_union_in _ _ P4) as [H1 [Q1 Q2]].
      destruct (subset_elim _ _ _ Q1) as [_ [Q3 [_ [_ [_ [_ Q4]]]]]].
      rewrite (fval_intro _ _ _ Q3 Q2).
      destruct (Q4 _ P2 (dom_intro _ _ (in_dom_intro _ _ _ Q2))) as [Q5 Q6].
      rewrite Q6.
      destruct (in_union_in _ _ P5) as [H2 [R1 R2]].
      destruct (subset_elim _ _ _ R1) as [_ [R3 [_ [_ [_ [_ R4]]]]]].
      rewrite (fval_intro _ _ _ R3 R2).
      destruct (R4 _ P2 (dom_intro _ _ (in_dom_intro _ _ _ R2))) as [R5 R6].
      rewrite R6.
      f_equal.
      apply P3.
      + apply in_in_union.
        exists H1.
        split.
        - apply Q1.
        - apply (fval_intro_2 _ _ Q3 Q5).
      + apply in_in_union.
        exists H2.
        split.
        - apply R1.
        - apply (fval_intro_2 _ _ R3 R5). }
    destruct (LEM (a0 ∈ ω)) as [P3|P3].
    - apply (induction_principle _ P1 P2 a0 P3).
    - intros b1 b2 P4 _.
      absurd (⟨a0, b1⟩ ∈ h).
      * apply not_in_dom.
        intros P5.
        destruct (in_union_in _ _ P4) as [hi [P6 P7]].
        destruct (subset_elim _ _ _ P6) as [_ [_ [P8 _]]].
        pose (P8 _ (dom_intro _  _ (in_dom_intro _ _ _ P7))) as P9.
        contradiction.
      * apply P4.
Qed.

Lemma _rec_single_pair_accept: forall A a F, a ∈ A ->
  ({⟨∅, a⟩}) ∈ (subset_ctor (_rec_accept F A a) (𝒫(cp ω A))).
Proof.
  intros A a F P1.
  pose (H := subset_ctor (_rec_accept F A a) (𝒫(cp ω A))).
  pose (h := ∪(H)).
  apply subset_intro.
  { apply subset_in_power.
    intros x P2.
    rewrite <- (in_singleton_equal _ _ P2).
    apply cp_intro.
    + apply empty_in_omega.
    + apply P1. }
  split.
  { apply single_pair_is_function. }
  split.
  { intros x P2.
    rewrite (single_pair_dom ∅ a) in P2. 
    rewrite <- (in_singleton_equal _ _ P2).
    apply empty_in_omega. }
  split.
  { intros x P2.
    rewrite (single_pair_ran ∅ a) in P2. 
    rewrite <- (in_singleton_equal _ _ P2).
    apply P1. }
  split.
  { rewrite (single_pair_dom ∅ a). 
    apply in_singleton. }
  split.
  { symmetry. 
    apply fval_intro.
    + apply single_pair_is_function. 
    + apply in_singleton. }
  { intros n P3 P4.
    rewrite (single_pair_dom ∅ a) in P4. 
    absurd (∅ = S(n)).
    + apply empty_not_suc.
    + apply (in_singleton_equal _ _ P4). }
Qed.

Lemma _rec_union_function: forall A a F f x y, a ∈ A -> fover F A A -> 
  S(x) ∉  dom(f) -> ⟨x, y⟩ ∈ f -> x ∈ ω -> 
  f ∈ (subset_ctor (_rec_accept F A a) (𝒫(cp ω A))) ->
  function (f ∪ ({⟨S(x), F[y]⟩})).
Proof. 
  intros A a F f x y P1 P2 P3 P4 P5 P6.
  pose (H := subset_ctor (_rec_accept F A a) (𝒫(cp ω A))).
  pose (h := ∪(H)).
  { apply piecewise_function. 
    + destruct (subset_elim _ _ _ P6) as [_ [Q1 _]].
      apply Q1.
    + apply single_pair_is_function.
    + apply ax_exten.
      intros z.
      split.
      - intros Q1.
        destruct (in_inter2_in _ _ _ Q1) as [Q2 Q3].
        rewrite single_pair_dom in Q3.
        rewrite <- (in_singleton_equal _ _ Q3) in Q2.
        contradiction.
      - intros Q1.
        pose (not_in_empty z) as Q2.
        contradiction. }
Qed.

Lemma _rec_union_accept: forall A a F f x y, a ∈ A -> fover F A A -> 
  S(x) ∉  dom(f) -> ⟨x, y⟩ ∈ f -> x ∈ ω -> 
  f ∈ (subset_ctor (_rec_accept F A a) (𝒫(cp ω A))) ->
  (f ∪ ({⟨S(x), F[y]⟩})) ∈ (subset_ctor (_rec_accept F A a) (𝒫(cp ω A))).
Proof.
  intros A a F f x y P1 P2 P3 P4 P5 P6.
  pose (H := subset_ctor (_rec_accept F A a) (𝒫(cp ω A))).
  pose (h := ∪(H)).
  pose (g := f ∪ ({⟨S(x), F[y]⟩})).
  apply subset_intro.
  { apply subset_in_power.
    intros z Q1.
    destruct (in_union2_in _ _ _ Q1) as [Q2|Q2].
    + destruct (subset_elim _ _ _ P6) as [Q3 _].
      apply (in_power_subset _ _ Q3 _ Q2).
    + rewrite <- (in_singleton_equal _ _ Q2). 
      apply cp_intro.
      - apply (suc_in_omega _ P5).
      - destruct P2 as [Q3 [Q4 Q5]]. 
        apply Q5.
        apply (fval_ran).
        * apply Q3.
        * rewrite Q4. 
          destruct (subset_elim _ _ _ P6) as [_ [_ [_ [Q6 _]]]].
          apply (Q6 _ (ran_intro _ _ (in_ran_intro _ _ _ P4))). }
  split.
  { apply (_rec_union_function _ _ _ _ _ _ P1 P2 P3 P4 P5 P6). }
  split.
  { intros z Q1.
    rewrite (union2_dom) in Q1.
    destruct (in_union2_in _ _ _ Q1) as [Q2|Q2].
    + destruct (subset_elim _ _ _ P6) as [_ [_ [Q3 _]]].
      apply (Q3 _ Q2).
    + rewrite single_pair_dom in Q2.
      rewrite <- (in_singleton_equal _ _ Q2).
      apply (suc_in_omega _ P5). }
  split.
  { intros z Q1.
    rewrite (union2_ran) in Q1.
    destruct (in_union2_in _ _ _ Q1) as [Q2|Q2].
    + destruct (subset_elim _ _ _ P6) as [_ [_ [_ [Q3 _]]]].
      apply (Q3 _ Q2).
    + rewrite single_pair_ran in Q2.
      rewrite <- (in_singleton_equal _ _ Q2).
      destruct P2 as [Q3 [Q4 Q5]].
      apply Q5.
      apply fval_ran. 
      - apply Q3.
      - rewrite Q4.
        destruct (subset_elim _ _ _ P6) as [_ [_ [_ [Q6 _]]]].
        apply (Q6 _ (ran_intro _ _ (in_ran_intro _ _ _ P4))). }
  split.
  { rewrite union2_dom. 
    apply in_in_union2_1.
    destruct (subset_elim _ _ _ P6) as [_ [_ [_ [_ [Q1 _]]]]].
    apply Q1. }
  split.
  { symmetry. 
    apply fval_intro.
    + apply (_rec_union_function _ _ _ _ _ _ P1 P2 P3 P4 P5 P6).
    + apply in_in_union2_1.
      destruct (subset_elim _ _ _ P6) as [_ [Q1 [_ [_ [Q2 [Q3 _]]]]]].
      rewrite <- Q3.
      apply (fval_intro_2 _ _ Q1 Q2). }
  { intros n Q1 Q2.
    rewrite union2_dom.
    rewrite union2_dom in Q2.
    destruct (in_union2_in _ _ _ Q2) as [Q3|Q3].
    + split. 
      - apply in_in_union2_1.
        destruct (subset_elim _ _ _ P6) as [_ [_ [_ [_ [_ [_ Q4]]]]]].
        destruct (Q4 _ Q1 Q3) as [Q5 _].
        apply Q5.
      - destruct (subset_elim _ _ _ P6) as [_ [Q4 [_ [_ [_ [_ Q5]]]]]].
        destruct (Q5 _ Q1 Q3) as [Q6 Q7].
        rewrite <- (union2_fval_1 _ _ _ Q4 (_rec_union_function _ _ _ _ _ _ P1 P2 P3 P4 P5 P6) Q3).
        rewrite <- (union2_fval_1 _ _ _ Q4 (_rec_union_function _ _ _ _ _ _ P1 P2 P3 P4 P5 P6) Q6).
        apply Q7.
    + split. 
      - rewrite single_pair_dom in Q3.
        apply in_in_union2_1.
        rewrite <- (suc_unique _ _ P5 Q1 (in_singleton_equal _ _ Q3)).
        apply dom_intro.
        exists y.
        apply P4. 
      - assert (x = n) as QQ. 
        { rewrite single_pair_dom in Q3.
          apply (suc_unique _ _ P5 Q1 (in_singleton_equal _ _ Q3)). }
        destruct (subset_elim _ _ _ P6) as [_ [Q4 [_ [_ [_ [_ _]]]]]].
        rewrite <- (union2_fval_2 _ _ _ (single_pair_is_function (S(x)) 
          (F[y])) (_rec_union_function _ _ _ _ _ _ P1 P2 P3 P4 P5 P6) Q3).
        assert (n ∈ dom(f)) as Q5.
        { apply dom_intro.
          exists y.
          rewrite <- QQ.
          apply P4. }
        rewrite <- (union2_fval_1 _ _ _ Q4 (_rec_union_function _ _ _ _ _ _ P1 P2 P3 P4 P5 P6) Q5).
        symmetry.
        apply fval_intro.
        * apply (single_pair_is_function (S(x)) (F[y])).
        * assert (y = f[n]) as Q6.
          { apply fval_intro.
            + apply Q4.
            + rewrite <- QQ.
              apply P4. }
          rewrite Q6.
          rewrite QQ.
          apply in_singleton. }
Qed.

Lemma _rec_dom: forall A a F, a ∈ A -> fover F A A ->
  dom(∪(subset_ctor (_rec_accept F A a) (𝒫(cp ω A)))) = ω.
Proof.
  intros A a F P1 S1.
  pose (H := subset_ctor (_rec_accept F A a) (𝒫(cp ω A))).
  pose (h := ∪(H)).
  assert (inductive (dom(h))) as P2.
  { split.
    + apply dom_intro.
      exists a.
      apply (in_in_union).
      exists ({⟨∅, a⟩}).
      split.
      - apply (_rec_single_pair_accept _ _ _ P1). 
      - apply in_singleton.
    + intros x P2.
      destruct (dom_elim _ _ P2) as [y P3].
      destruct (in_union_in _ _ P3) as [f [P4 P5]].
      apply dom_intro.
      destruct (LEM (S(x) ∈ dom(f))) as [P6|P6].
      - exists (f[S(x)]).
        apply in_in_union.
        exists f.
        split.
        * apply P4.
        * destruct (subset_elim _ _ _ P4) as [_ [P7 _]]. 
          apply (fval_intro_2 _ _ P7 P6).
      - pose (g := f ∪ ({⟨S(x), F[y]⟩})).
        exists (g[S(x)]).
        apply in_in_union.
        exists ( f ∪ ({⟨S(x), F[y]⟩})).
        assert (x ∈ ω) as P7. 
        { destruct (subset_elim _ _ _ P4) as [_ [_ [P7 _]]].
          apply P7.
          apply dom_intro.
          exists y.
          apply P5. }
        split.
        * apply (_rec_union_accept _ _ _ _ _ _ P1 S1 P6 P5 P7 P4).
        * destruct (subset_elim _ _ _ P4) as [_ [P8 _]]. 
          apply (fval_intro_2).
          apply (_rec_union_function _ _ _ _ _ _ P1 S1 P6 P5 P7 P4).
          rewrite union2_dom.
          apply in_in_union2_2.
          rewrite single_pair_dom.
          apply in_singleton. }
  assert (dom(h) ⊆ ω) as P3.
  { intros x P3.
    destruct (dom_elim _ _ P3) as [y P4].
    destruct (in_union_in _ _ P4) as [f [P5 P6]].
    destruct (subset_elim _ _ _ P5) as [_ [_ [P7 _]]].
    apply (P7 _ (dom_intro _ _ (in_dom_intro _ _ _ P6))). }
  apply (inductive_subset_omega_coincident _ P3 P2).
Qed.

Lemma _rec_ran: forall A a F, a ∈ A ->
  ran(∪(subset_ctor (_rec_accept F A a) (𝒫(cp ω A)))) ⊆ A.
Proof.
  intros A a F P1 y P2.
  destruct (ran_elim _ _ P2) as [x P3].
  destruct (in_union_in _ _ P3) as [f [P4 P5]].
  destruct (subset_elim _ _ _ P4) as [_ [_ [_ [P6 _]]]].
  apply (P6 _ (ran_intro _ _ (in_ran_intro _ _ _ P5))).
Qed.

Theorem recursion_theorem: forall A a F, exists h, a ∈ A -> fover F A A ->
    fover h ω A /\ h[∅] = a /\ (forall n, n ∈ ω -> h[S(n)] = F[h[n]]).
Proof.
  intros A a F.
  pose (P := _rec_accept F A a).
  pose (H := subset_ctor P (𝒫(cp ω A))).
  pose (h := ∪(H)).
  exists h.
  intros P1 P2.
  split.
  (* fover h ω A *)
  { split.
    + apply _rec_fun.
    + split.
      - apply (_rec_dom _ _ _ P1 P2).
      - apply (_rec_ran _ _ _ P1). }
  split.
  { symmetry. 
    apply fval_intro.
    + apply _rec_fun.
    + apply (in_in_union).
      exists ({⟨∅, a⟩}).
      split.
      - apply (_rec_single_pair_accept _ _ _ P1).
      - apply in_singleton. } 
  { intros n P3.
    assert (S(n) ∈ dom(h)) as P4.
    { pose (suc_in_omega _ P3) as P4.
      rewrite <- (_rec_dom A a F P1 P2) in P4.
      apply P4. }
    destruct (dom_elim _ _ P4) as [y P5].
    destruct (in_union_in _ _ P5) as [f [P6 P7]].
    destruct (subset_elim _ _ _ P6) as [_ [P8 [_ [_ [_ [_ P9]]]]]].
    destruct (P9 n P3 (dom_intro _ _ (in_dom_intro _ _ _ P7))) as [P10 P11].
    rewrite (union_fval _ _ _ P6 P8 (_rec_fun A a F) 
      (dom_intro _ _ (in_dom_intro _ _ _ P7))) in P11.
    rewrite (union_fval _ _ _ P6 P8 (_rec_fun A a F) P10) in P11.
    apply P11. }
Qed.
(*----------------------------------------------------------------------------*)
