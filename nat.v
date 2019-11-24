Require Import logic.
Require Import axiom.
Require Import basic.
Require Import relation.

Lemma suc_elim: forall A x, x ∈ S(A) -> x = A \/ x ∈ A.
Proof.
  intros A x P1.
  destruct (in_union2_in _ _ _ P1) as [P2|P2].
  + right.
    apply P2.
  + left.
    symmetry.
    apply (in_singleton_equal _ _ P2).
Qed.

Lemma suc_intro_1: forall A, A ∈ S(A).
Proof.
  intros A.
  apply in_in_union2_2.
  apply in_singleton.
Qed.

Lemma suc_intro_2: forall A x, x ∈ A -> x ∈ S(A).
Proof.
  intros A.
  apply in_in_union2_1.
Qed.

Definition nat (n: set) := forall B, inductive B -> n ∈ B.
Theorem omega_exists: exists A, forall n, nat n <-> n ∈ A.
Proof.
  destruct ax_infinity as [X P1].
  exists (subset_ctor (fun n => forall B, inductive B -> n ∈ B) X). 
  intros n.
  split.
  + intros P2.
    apply subset_intro.
    - apply (P2 X P1).
    - intros B P3.
      apply (P2 B P3).
  + apply subset_elim.
Qed.

Definition ω := extract_set omega_exists.

Lemma omega_intro: forall x, nat x -> x ∈ ω.
Proof.
  intros x P1.
  destruct (extract_set_property omega_exists x) as [P2 _].
  apply (P2 P1).
Qed.

Lemma omega_elim: forall x, x ∈ ω-> nat x.
Proof.
  intros x P1.
  destruct (extract_set_property omega_exists x) as [_ P2].
  apply (P2 P1).
Qed.

Lemma omega_inductive: inductive ω.
Proof.
  split.
  + apply omega_intro.
    intros A [P1 _].
    apply P1.
  + intros x P1.
    apply omega_intro.
    intros A P2.
    pose (omega_elim x P1 A P2) as P3.
    destruct P2 as [P4 P5].
    apply (P5 x P3).
Qed.

Lemma omega_is_subset: forall A, inductive A -> ω ⊆ A.
Proof.
  intros A P1 x P2.
  apply (omega_elim x P2 A P1).
Qed.

Lemma empty_in_omega: ∅ ∈ ω.
Proof.
  apply omega_intro.
  intros B P1.
  destruct P1 as [P2 _].
  apply P2.
Qed.

Lemma suc_in_omega: forall k, k ∈ ω -> S(k) ∈ ω.
Proof.
  intros k P1.
  apply omega_intro.
  intros B P2.
  pose ((omega_elim _ P1) B P2) as P3.
  destruct P2 as [P2 P4].
  apply (P4 _ P3).
Qed.

Lemma suc_is_nat: forall k, nat k -> nat (S(k)).
Proof. 
  intros k P1.
  apply omega_elim.
  apply suc_in_omega.
  apply omega_intro.
  apply P1.
Qed.

Lemma induction_principle_: forall T, T ⊆ ω -> inductive T -> T = ω.
Proof.
  intros T P1 P2.
  apply subset_asym.
  apply (conj P1 (omega_is_subset T P2)).
Qed.

Lemma induction_principle: forall P: set -> Prop, P ∅ ->
  (forall k, k ∈ ω -> P k -> P (S(k))) -> (forall n, n ∈ ω -> P n).
Proof.
  intros P P1 P2 n P3.
  assert ((subset_ctor P ω) ⊆ ω) as P4.
  { intros x.
    intros P5.
    destruct (subset_elim _ _ _ P5) as [P6 _].
    apply P6. }
  assert (inductive (subset_ctor P ω)) as P5.
  { split.
    + apply (subset_intro _ _ _ (empty_in_omega) P1).
    + intros x P5.
      destruct (subset_elim _ _ _ P5) as [P6 P7].
      apply (subset_intro _ _ _ (suc_in_omega _ P6) (P2 _ P6 P7)). }
  rewrite <- (induction_principle_ _ P4 P5) in P3.
  destruct (subset_elim _ _ _ P3) as [_ P6].
  apply P6.
Qed.
    
Lemma nat_is_suc: forall x, x ∈ ω -> x <> ∅ -> exists y, y ∈ ω /\ x = S(y).
Proof.
  intros x P1 P2.
  pose (P := fun x => x = ∅ \/ exists y, y ∈ ω /\ x = S(y)).
  assert (P ∅) as P3.
  { left.
    reflexivity. }
  assert (forall k, k ∈ ω -> P k -> P (S(k))) as P4.
  { intros k P5 [P4|P4].
    + right.
      exists ∅.
      rewrite P4.
      split.
      - apply empty_in_omega. 
      - reflexivity.
    + right.
      exists k.
      split.
      - apply P5. 
      - reflexivity. }
  destruct (induction_principle _ P3 P4 x P1) as [P5|P5].
  + contradiction.
  + apply P5.
Qed.

Lemma empty_not_suc: forall x, ∅ <> S(x).
Proof.
  intros x P1.
  absurd (x ∈ ∅).
  + apply not_in_empty.
  + rewrite P1.
    apply suc_intro_1.
Qed.
    
(* Skip Peano's System *)

(* Transition *)
Definition trans (A: set) := forall x a, x ∈ a /\ a ∈ A -> x ∈ A.

Lemma trans_elim_1: forall A, trans A -> ∪(A) ⊆ A.
Proof.
  intros A P1 x P2.
  destruct (in_union_in A x P2) as [a P3].
  apply (P1 _ _ (and_sym _ _ P3)).
Qed.

Lemma trans_elim_2: forall A, trans A -> forall a, a ∈ A -> a ⊆ A.
Proof. 
  intros A P1 a P2 x P3.
  apply (P1 _ _ (conj P3 P2)).
Qed.

Lemma trans_elim_3: forall A, trans A -> A ⊆ 𝒫(A).
Proof.
  intros A P1 x P2.
  apply subset_in_power.
  apply (trans_elim_2 _ P1 _ P2).
Qed.

Lemma trans_intro_1: forall A, ∪(A) ⊆ A -> trans A.
Proof.
  intros A P1 x a P2.
  apply P1.
  apply (in_in_union).
  exists a.
  apply (and_sym _ _ P2).
Qed.

Lemma trans_intro_2: forall A, (forall a, a ∈ A -> a ⊆ A) -> trans A.
Proof.
  intros A P1 x a [P2 P3].
  apply (P1 _ P3 x P2).
Qed.

Lemma trans_intro_3: forall A, A ⊆ 𝒫(A) -> trans A.
Proof.
  intros A P1 x a [P2 P3].
  apply (in_power_subset _ _ (P1 _ P3) x P2).
Qed.

Lemma union_trans_suc: forall A, trans A -> ∪(S(A)) = A.
Proof.
  intros A P1.
  apply ax_exten.
  intros x.
  split.
  + intros P2.
    destruct (in_union_in _ _ P2) as [y [P3 P4]].
    destruct (suc_elim _ _ P3) as [P5|P5].
    - rewrite <- P5.
      apply P4.
    - apply (P1 _ _ (conj P4 P5)).
  + intros P2.
    apply (in_in_union).
    exists A.
    split.
    - apply suc_intro_1.
    - apply P2.
Qed.

(* 4F *)
Lemma nat_is_trans: forall A, nat A -> trans A.
Proof.
  intros A P1.
  assert (trans ∅) as P2.
  { intros x a [_ P2].
    absurd (a ∈ ∅).
    + apply not_in_empty.
    + apply P2. }
  assert (forall k, k ∈ ω -> trans k -> trans (S(k))) as P3.
  { intros k _ P3.
    apply trans_intro_1.
    rewrite (union_trans_suc _ P3).
    intros x P4.
    apply (suc_intro_2 _ _ P4). }
  pose (omega_intro _ P1) as P4.
  apply (induction_principle _ P2 P3 A P4).
Qed.

(* 4G *)
Lemma omega_is_trans: trans ω.
Proof. 
  assert (∅ ⊆ ω) as P1.
  { intros x P1.
    absurd (x ∈ ∅).
    + apply not_in_empty.
    + apply P1. }
  assert (forall k, k ∈ ω -> k ⊆ ω -> S(k) ⊆ ω) as P2.
  { intros k P2 P3 x P4.
    destruct (suc_elim _ _ P4) as [P5|P5].
    + rewrite P5.
      apply P2.
    + apply (P3 _ P5). }
  apply (trans_intro_2 _ (induction_principle _ P1 P2)).
Qed.

Lemma nat_not_in_self: forall n, n ∈ ω -> n ∉  n.
Proof.
  intros n P1.
  assert (∅ ∉  ∅) as P2.
  { apply not_in_empty. }
  assert (forall k, k ∈ ω -> k ∉  k -> S(k) ∉  S(k)) as P3.
  { intros k P3 P4 P5.
    absurd (k ∈ k). 
    + apply P4.
    + destruct (suc_elim _ _ P5) as [P6|P6].
      - pose (P7 := suc_intro_1 k).
        rewrite P6 in P7.
        apply P7.
      - pose (P7 := suc_intro_1 k).
        apply (nat_is_trans _ (omega_elim _ P3) _ _ (conj P7 P6)). }
  apply (induction_principle _ P2 P3 _ P1).
Qed.

Lemma suc_unique: forall x y, x ∈ ω -> y ∈ ω -> S(x) = S(y) -> x = y.
Proof. 
  intros x y P1 P2 P3.
  pose (suc_intro_1 x) as P4.
  rewrite P3 in P4.
  destruct (suc_elim _ _ P4) as [P5|P5].
  + apply P5.
  + pose (suc_intro_1 y) as P6.
    rewrite <- P3 in P6.
    destruct (suc_elim _ _ P6) as [P7|P7].
    - symmetry. 
      apply P7.
    - absurd (x ∈ x). 
      * apply (nat_not_in_self _ P1). 
      * apply (nat_is_trans _ (omega_elim _ P1) _ _ (conj P5 P7)).
Qed.

(* Recursion Theorem *)
Definition _rec_accept (F: set) (A: set) (a: set) := fun f => 
    function f /\ dom(f) ⊆ ω /\ ran(f) ⊆ A /\ ∅ ∈ dom(f) /\ fun_val f ∅ = a /\ 
    (forall n, n ∈ ω-> S(n) ∈ dom(f) -> 
      n ∈ dom(f) /\ fun_val f (S(n)) = fun_val F (fun_val f n)).

Lemma _rec_fun: forall A a F, function (∪(subset_ctor (_rec_accept F A a) (𝒫(cp ω A)))).
Proof.
  intros A a F.
  pose (H := subset_ctor (_rec_accept F A a) (𝒫(cp ω A))).
  pose (h := ∪(H)).
  split.
  + apply union_relation.
    intros f P1.
    destruct (subset_elim _ _ _ P1) as [_ [[P2 _] _]].
    apply P2.
  + intros a0. 
    pose (PI := fun x => forall b1 b2, ⟨x, b1⟩ ∈ h /\ ⟨x, b2⟩ ∈ h -> b1 = b2).
    assert (PI ∅) as P1.
    { intros b1 b2 [P2 P3].
      destruct (in_union_in _ _ P2) as [H1 [Q1 Q2]].
      destruct (subset_elim _ _ _ Q1) as [_ [Q3 [_ [_ [Q4 [Q5 _]]]]]].
      symmetry in Q5.
      destruct (fun_val_elim _ _ _ Q5 Q3 Q4) as [_ Q6].
      rewrite <- (Q6 _ Q2).
      destruct (in_union_in _ _ P3) as [H2 [R1 R2]].
      destruct (subset_elim _ _ _ R1) as [_ [R3 [_ [_ [R4 [R5 _]]]]]].
      symmetry in R5.
      destruct (fun_val_elim _ _ _ R5 R3 R4) as [_ R6].
      apply (R6 _ R2). }
    assert (forall k, k ∈ ω -> PI k -> PI (S(k))) as P2. 
    { intros k P2 P3 b1 b2 [P4 P5].
      destruct (in_union_in _ _ P4) as [H1 [Q1 Q2]].
      destruct (subset_elim _ _ _ Q1) as [_ [Q3 [_ [_ [_ [_ Q4]]]]]].
      rewrite (fun_val_intro _ _ _ Q3 (domain_intro _ _ (in_domain_intro _ _ _ Q2)) Q2).
      destruct (Q4 _ P2 (domain_intro _ _ (in_domain_intro _ _ _ Q2))) as [Q5 Q6].
      rewrite Q6.
      destruct (in_union_in _ _ P5) as [H2 [R1 R2]].
      destruct (subset_elim _ _ _ R1) as [_ [R3 [_ [_ [_ [_ R4]]]]]].
      rewrite (fun_val_intro _ _ _ R3 (domain_intro _ _ (in_domain_intro _ _ _ R2)) R2).
      destruct (R4 _ P2 (domain_intro _ _ (in_domain_intro _ _ _ R2))) as [R5 R6].
      rewrite R6.
      f_equal.
      apply P3.
      split.
      + apply in_in_union.
        exists H1.
        split.
        - apply Q1.
        - apply (fun_val_basic _ _ Q3 Q5).
      + apply in_in_union.
        exists H2.
        split.
        - apply R1.
        - apply (fun_val_basic _ _ R3 R5). }
    destruct (LEM (a0 ∈ ω)) as [P3|P3].
    - apply (induction_principle _ P1 P2 a0 P3).
    - intros b1 b2 [P4 _].
      absurd (⟨a0, b1⟩ ∈ h).
      * apply not_in_domain.
        intros P5.
        destruct (in_union_in _ _ P4) as [hi [P6 P7]].
        destruct (subset_elim _ _ _ P6) as [_ [_ [P8 _]]].
        pose (P8 _ (domain_intro _  _ (in_domain_intro _ _ _ P7))) as P9.
        contradiction.
      * apply P4.
Qed.

Lemma _rec_single_value_accept: forall A a F, a ∈ A ->
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
  { apply single_value_is_function. }
  split.
  { intros x P2.
    rewrite (single_value_domain ∅ a) in P2. 
    rewrite <- (in_singleton_equal _ _ P2).
    apply empty_in_omega. }
  split.
  { intros x P2.
    rewrite (single_value_range ∅ a) in P2. 
    rewrite <- (in_singleton_equal _ _ P2).
    apply P1. }
  split.
  { rewrite (single_value_domain ∅ a). 
    apply in_singleton. }
  split.
  { symmetry. 
    apply fun_val_intro.
    + apply single_value_is_function. 
    + rewrite (single_value_domain ∅ a). 
      apply in_singleton.
    + apply in_singleton. }
  { intros n P3 P4.
    rewrite (single_value_domain ∅ a) in P4. 
    absurd (∅ = S(n)).
    + apply empty_not_suc.
    + apply (in_singleton_equal _ _ P4). }
Qed.

Lemma _rec_union_function: forall A a F f x y, a ∈ A -> fun_maps F A A -> 
  S(x) ∉  dom(f) -> ⟨x, y⟩ ∈ f -> x ∈ ω -> 
  f ∈ (subset_ctor (_rec_accept F A a) (𝒫(cp ω A))) ->
  function (f ∪ ({⟨S(x), fun_val F y⟩})).
Proof. 
  intros A a F f x y P1 P2 P3 P4 P5 P6.
  pose (H := subset_ctor (_rec_accept F A a) (𝒫(cp ω A))).
  pose (h := ∪(H)).
  { apply piecewise_function. 
    + destruct (subset_elim _ _ _ P6) as [_ [Q1 _]].
      apply Q1.
    + apply single_value_is_function.
    + apply ax_exten.
      intros z.
      split.
      - intros Q1.
        destruct (in_inter2_in _ _ _ Q1) as [Q2 Q3].
        rewrite single_value_domain in Q3.
        rewrite <- (in_singleton_equal _ _ Q3) in Q2.
        contradiction.
      - intros Q1.
        pose (not_in_empty z) as Q2.
        contradiction. }
Qed.

Lemma _rec_union_accept: forall A a F f x y, a ∈ A -> fun_maps F A A -> 
  S(x) ∉  dom(f) -> ⟨x, y⟩ ∈ f -> x ∈ ω -> 
  f ∈ (subset_ctor (_rec_accept F A a) (𝒫(cp ω A))) ->
  (f ∪ ({⟨S(x), fun_val F y⟩})) ∈ (subset_ctor (_rec_accept F A a) (𝒫(cp ω A))).
Proof.
  intros A a F f x y P1 P2 P3 P4 P5 P6.
  pose (H := subset_ctor (_rec_accept F A a) (𝒫(cp ω A))).
  pose (h := ∪(H)).
  pose (g := f ∪ ({⟨S(x), fun_val F y⟩})).
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
        apply (fun_val_range).
        * apply Q3.
        * rewrite Q4. 
          destruct (subset_elim _ _ _ P6) as [_ [_ [_ [Q6 _]]]].
          apply (Q6 _ (range_intro _ _ (in_range_intro _ _ _ P4))). }
  split.
  { apply (_rec_union_function _ _ _ _ _ _ P1 P2 P3 P4 P5 P6). }
  split.
  { intros z Q1.
    rewrite (union2_domain) in Q1.
    destruct (in_union2_in _ _ _ Q1) as [Q2|Q2].
    + destruct (subset_elim _ _ _ P6) as [_ [_ [Q3 _]]].
      apply (Q3 _ Q2).
    + rewrite single_value_domain in Q2.
      rewrite <- (in_singleton_equal _ _ Q2).
      apply (suc_in_omega _ P5). }
  split.
  { intros z Q1.
    rewrite (union2_range) in Q1.
    destruct (in_union2_in _ _ _ Q1) as [Q2|Q2].
    + destruct (subset_elim _ _ _ P6) as [_ [_ [_ [Q3 _]]]].
      apply (Q3 _ Q2).
    + rewrite single_value_range in Q2.
      rewrite <- (in_singleton_equal _ _ Q2).
      destruct P2 as [Q3 [Q4 Q5]].
      apply Q5.
      apply fun_val_range. 
      - apply Q3.
      - rewrite Q4.
        destruct (subset_elim _ _ _ P6) as [_ [_ [_ [Q6 _]]]].
        apply (Q6 _ (range_intro _ _ (in_range_intro _ _ _ P4))). }
  split.
  { rewrite union2_domain. 
    apply in_in_union2_1.
    destruct (subset_elim _ _ _ P6) as [_ [_ [_ [_ [Q1 _]]]]].
    apply Q1. }
  split.
  { symmetry. 
    apply fun_val_intro.
    + apply (_rec_union_function _ _ _ _ _ _ P1 P2 P3 P4 P5 P6).
    + rewrite union2_domain. 
      apply in_in_union2_1.
      destruct (subset_elim _ _ _ P6) as [_ [_ [_ [_ [Q1 _]]]]].
      apply Q1.
    + apply in_in_union2_1.
      destruct (subset_elim _ _ _ P6) as [_ [Q1 [_ [_ [Q2 [Q3 _]]]]]].
      rewrite <- Q3.
      apply (fun_val_basic _ _ Q1 Q2). }
  { intros n Q1 Q2.
    rewrite union2_domain.
    rewrite union2_domain in Q2.
    destruct (in_union2_in _ _ _ Q2) as [Q3|Q3].
    + split. 
      - apply in_in_union2_1.
        destruct (subset_elim _ _ _ P6) as [_ [_ [_ [_ [_ [_ Q4]]]]]].
        destruct (Q4 _ Q1 Q3) as [Q5 _].
        apply Q5.
      - destruct (subset_elim _ _ _ P6) as [_ [Q4 [_ [_ [_ [_ Q5]]]]]].
        destruct (Q5 _ Q1 Q3) as [Q6 Q7].
        rewrite <- (union2_fun_equal_1 _ _ _ Q4 (single_value_is_function (S(x)) 
          (fun_val F y)) (_rec_union_function _ _ _ _ _ _ P1 P2 P3 P4 P5 P6) Q3).
        rewrite <- (union2_fun_equal_1 _ _ _ Q4 (single_value_is_function (S(x)) 
          (fun_val F y)) (_rec_union_function _ _ _ _ _ _ P1 P2 P3 P4 P5 P6) Q6).
        apply Q7.
    + split. 
      - rewrite single_value_domain in Q3.
        apply in_in_union2_1.
        rewrite <- (suc_unique _ _ P5 Q1 (in_singleton_equal _ _ Q3)).
        apply domain_intro.
        exists y.
        apply P4. 
      - assert (x = n) as QQ. 
        { rewrite single_value_domain in Q3.
          apply (suc_unique _ _ P5 Q1 (in_singleton_equal _ _ Q3)). }
        destruct (subset_elim _ _ _ P6) as [_ [Q4 [_ [_ [_ [_ _]]]]]].
        rewrite <- (union2_fun_equal_2 _ _ _ Q4 (single_value_is_function (S(x)) 
          (fun_val F y)) (_rec_union_function _ _ _ _ _ _ P1 P2 P3 P4 P5 P6) Q3).
        assert (n ∈ dom(f)) as Q5.
        { apply domain_intro.
          exists y.
          rewrite <- QQ.
          apply P4. }
        rewrite <- (union2_fun_equal_1 _ _ _ Q4 (single_value_is_function (S(x)) 
          (fun_val F y)) (_rec_union_function _ _ _ _ _ _ P1 P2 P3 P4 P5 P6) Q5).
        symmetry.
        apply fun_val_intro.
        * apply (single_value_is_function (S(x)) (fun_val F y)).
        * apply Q3.
        * assert (y = fun_val f n) as Q6.
          { apply fun_val_intro.
            + apply Q4.
            + apply Q5.
            + rewrite <- QQ.
              apply P4. }
          rewrite Q6.
          rewrite QQ.
          apply in_singleton. }
Qed.

Lemma _rec_domain: forall A a F, a ∈ A -> fun_maps F A A ->
  dom(∪(subset_ctor (_rec_accept F A a) (𝒫(cp ω A)))) = ω.
Proof.
  intros A a F P1 S1.
  pose (H := subset_ctor (_rec_accept F A a) (𝒫(cp ω A))).
  pose (h := ∪(H)).
  assert (inductive (dom(h))) as P2.
  { split.
    + apply domain_intro.
      exists a.
      apply (in_in_union).
      exists ({⟨∅, a⟩}).
      split.
      - apply (_rec_single_value_accept _ _ _ P1). 
      - apply in_singleton.
    + intros x P2.
      destruct (domain_elim _ _ P2) as [y P3].
      destruct (in_union_in _ _ P3) as [f [P4 P5]].
      apply domain_intro.
      destruct (LEM (S(x) ∈ dom(f))) as [P6|P6].
      - exists (fun_val f (S(x))).
        apply in_in_union.
        exists f.
        split.
        * apply P4.
        * destruct (subset_elim _ _ _ P4) as [_ [P7 _]]. 
          apply (fun_val_basic _ _ P7 P6).
      - pose (g := f ∪ ({⟨S(x), fun_val F y⟩})).
        exists (fun_val g (S(x))).
        apply in_in_union.
        exists ( f ∪ ({⟨S(x), fun_val F y⟩})).
        assert (x ∈ ω) as P7. 
        { destruct (subset_elim _ _ _ P4) as [_ [_ [P7 _]]].
          apply P7.
          apply domain_intro.
          exists y.
          apply P5. }
        split.
        * apply (_rec_union_accept _ _ _ _ _ _ P1 S1 P6 P5 P7 P4).
        * destruct (subset_elim _ _ _ P4) as [_ [P8 _]]. 
          apply (fun_val_basic).
          apply (_rec_union_function _ _ _ _ _ _ P1 S1 P6 P5 P7 P4).
          rewrite union2_domain.
          apply in_in_union2_2.
          rewrite single_value_domain.
          apply in_singleton. }
  assert (dom(h) ⊆ ω) as P3.
  { intros x P3.
    destruct (domain_elim _ _ P3) as [y P4].
    destruct (in_union_in _ _ P4) as [f [P5 P6]].
    destruct (subset_elim _ _ _ P5) as [_ [_ [P7 _]]].
    apply (P7 _ (domain_intro _ _ (in_domain_intro _ _ _ P6))). }
  apply (induction_principle_ _ P3 P2).
Qed.

Lemma _rec_range: forall A a F, a ∈ A ->
  ran(∪(subset_ctor (_rec_accept F A a) (𝒫(cp ω A)))) ⊆ A.
Proof.
  intros A a F P1 y P2.
  destruct (range_elim _ _ P2) as [x P3].
  destruct (in_union_in _ _ P3) as [f [P4 P5]].
  destruct (subset_elim _ _ _ P4) as [_ [_ [_ [P6 _]]]].
  apply (P6 _ (range_intro _ _ (in_range_intro _ _ _ P5))).
Qed.

Theorem recursion_theorem: forall A a F, exists h, a ∈ A -> fun_maps F A A ->
    fun_maps h ω A /\ (fun_val h ∅) = a /\ 
    (forall n, n ∈ ω -> fun_val h (S(n)) = fun_val F (fun_val h n)).
Proof.
  intros A a F.
  pose (P := _rec_accept F A a).
  pose (H := subset_ctor P (𝒫(cp ω A))).
  pose (h := ∪(H)).
  exists h.
  intros P1 P2.
  split.
  (* fun_maps h ω A *)
  { split.
    + apply _rec_fun.
    + split.
      - apply (_rec_domain _ _ _ P1 P2).
      - apply (_rec_range _ _ _ P1). }
  split.
  { symmetry. 
    apply fun_val_intro.
    + apply _rec_fun.
    + apply domain_intro.
      exists a.
      apply (in_in_union).
      exists ({⟨∅, a⟩}).
      split.
      - apply (_rec_single_value_accept _ _ _ P1).
      - apply in_singleton.
    + apply (in_in_union).
      exists ({⟨∅, a⟩}).
      split.
      - apply (_rec_single_value_accept _ _ _ P1).
      - apply in_singleton. } 
  { intros n P3.
    assert (S(n) ∈ dom(h)) as P4.
    { pose (suc_in_omega _ P3) as P4.
      rewrite <- (_rec_domain A a F P1 P2) in P4.
      apply P4. }
    destruct (domain_elim _ _ P4) as [y P5].
    destruct (in_union_in _ _ P5) as [f [P6 P7]].
    destruct (subset_elim _ _ _ P6) as [_ [P8 [_ [_ [_ [_ P9]]]]]].
    destruct (P9 n P3 (domain_intro _ _ (in_domain_intro _ _ _ P7))) as [P10 P11].
    rewrite (union_fun_equal _ _ _ P6 P8 (_rec_fun A a F) 
      (domain_intro _ _ (in_domain_intro _ _ _ P7))) in P11.
    rewrite (union_fun_equal _ _ _ P6 P8 (_rec_fun A a F) P10) in P11.
    apply P11. }
Qed.
  
(* Arithmetic *)
Definition σ := subset_ctor (fun x => exists y, x = ⟨y, S(y)⟩) (cp ω ω).
Lemma sigma_is_function: fun_maps σ ω ω.
Proof.
  split.
  split.
  { intros x P1.
    destruct (subset_elim _ _ _ P1) as [_ [y P2]].
    exists y.
    exists (S(y)).
    apply P2. }
  { intros a b1 b2 [P1 P2].
    destruct (subset_elim _ _ _ P1) as [_ [y1 P3]].
    destruct (opair_equal_elim _ _ _ _ P3) as [P4 P5].
    rewrite P5.
    rewrite <- P4.
    destruct (subset_elim _ _ _ P2) as [_ [y2 P6]].
    destruct (opair_equal_elim _ _ _ _ P6) as [P7 P8].
    rewrite P8.
    rewrite <- P7.
    reflexivity. }
  split.
  { apply ax_exten.
    intros x.
    split.
    + intros P1.
      destruct (domain_elim _ _ P1) as [y P2].
      destruct (subset_elim _ _ _ P2) as [P3 _].
      destruct (cp_elim _ _ _ P3) as [nx [ny [P4 [_ P5]]]].
      destruct (opair_equal_elim _ _ _ _ P5) as [P6 _].
      rewrite P6.
      apply P4.
    + intros P2.
      apply domain_intro.
      exists (S(x)).
      apply subset_intro.
      - apply cp_intro.
        * apply P2.
        * apply (suc_in_omega _ P2).
      - exists x.
        reflexivity. }
    { intros y P1.
      destruct (range_elim _ _ P1) as [x P2].
      destruct (subset_elim _ _ _ P2) as [P3 _].
      destruct (cp_elim _ _ _ P3) as [nx [ny [_ [P4 P5]]]].
      destruct (opair_equal_elim _ _ _ _ P5) as [_ P6].
      rewrite P6.
      apply P4. }
Qed.

Lemma sigma_intro: forall k, k ∈ ω -> S(k) = fun_val σ k.
Proof.
  intros k P1.
  apply fun_val_intro.
  + destruct sigma_is_function as [P2 _].
    apply P2.
  + destruct sigma_is_function as [_ [P2 _]].
    rewrite P2.
    apply P1.
  + apply subset_intro.
    - apply cp_intro.
      * apply P1.
      * apply (suc_in_omega _ P1).
    - exists k.
      reflexivity.
Qed.

Definition add_proto (m: set) :=
  extract_set (recursion_theorem ω m σ).

Lemma add_proto_is_function: forall m, m ∈ ω -> fun_maps (add_proto m) ω ω.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω m σ) P1 sigma_is_function)
    as [P2 _].
  apply P2.
Qed.

Lemma add_proto_elim_1: forall m, m ∈ ω -> fun_val (add_proto m) ∅ = m.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω m σ) P1 sigma_is_function) 
    as [_ [P2 _]].
  apply P2.
Qed.

Lemma add_proto_elim_2: forall m n, m ∈ ω -> n ∈ ω -> 
    fun_val (add_proto m) (S(n)) = S(fun_val (add_proto m) n).
Proof.
  intros m n P1 P2.
  destruct (extract_set_property (recursion_theorem ω m σ) P1 sigma_is_function) 
    as [[P3 [P4 P5]] [_ P6]].
  assert ((fun_val (extract_set (recursion_theorem ω m σ)) n) ∈ ω) as P7.
  { apply P5. 
    apply fun_val_range.
    + apply P3.
    + rewrite P4.
      apply P2. }
  pose (P6 n) as P8.
  rewrite <- (sigma_intro _ P7) in P8.
  apply P8.
  apply P2.
Qed.
    
Notation "m ₙ+ n" := (fun_val (add_proto m) n) (at level 65, no associativity).

Notation "ₙ0" := ∅       (at level 60, no associativity).
Notation "ₙ1" := (S(ₙ0)) (at level 60, no associativity).
Notation "ₙ2" := (S(ₙ1)) (at level 60, no associativity).
Notation "ₙ3" := (S(ₙ2)) (at level 60, no associativity).
Notation "ₙ4" := (S(ₙ3)) (at level 60, no associativity).

Lemma add_zero: forall m, m ∈ ω -> m ₙ+ ₙ0 = m.
Proof.
  intros m P1.
  apply (add_proto_elim_1 _ P1).
Qed.

Lemma add_red: forall m n, m ∈ ω -> n ∈ ω -> m ₙ+ S(n) = S(m ₙ+ n).
Proof.
  intros m n P1 P2.
  apply (add_proto_elim_2 _ _ P1 P2).
Qed.

Lemma add_in_omega: forall m n, m ∈ ω -> n ∈ ω -> m ₙ+ n ∈ ω.
Proof.
  intros m n P1 P2.
  destruct (add_proto_is_function _ P1) as [P3 [P4 P5]].
  apply P5.
  apply range_intro.
  exists n.
  apply fun_val_basic.
  + apply P3.
  + rewrite P4.
    apply P2.
Qed.

Theorem one_one_two: ₙ1 ₙ+ ₙ1 = ₙ2.
Proof.
  assert (ₙ1 ∈ ω) as P1.
  { apply suc_in_omega. 
    apply empty_in_omega. }
  rewrite (add_red (ₙ1) (ₙ0) P1 empty_in_omega).
  rewrite (add_zero (ₙ1) P1).
  reflexivity.
Qed.

Definition multi_proto (m: set) :=
  extract_set (recursion_theorem ω (ₙ0) (add_proto m)).

Lemma multi_proto_is_function: forall m, m ∈ ω -> fun_maps (multi_proto m) ω ω.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω (ₙ0) (add_proto m)) 
    (empty_in_omega) (add_proto_is_function _ P1)) as [P2 _].
  apply P2.
Qed.

Lemma multi_proto_elim_1: forall m, m ∈ ω -> fun_val (multi_proto m) ∅ = ∅.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω (ₙ0) (add_proto m)) 
    (empty_in_omega) (add_proto_is_function _ P1)) as [_ [P2 _]].
  apply P2.
Qed.

Lemma multi_proto_elim_2: forall m n, m ∈ ω -> n ∈ ω -> 
    fun_val (multi_proto m) (S(n)) = fun_val (add_proto m) (fun_val (multi_proto m) n).
Proof.
  intros m n P1 P2.
  destruct (extract_set_property (recursion_theorem ω (ₙ0) (add_proto m)) 
    (empty_in_omega) (add_proto_is_function _ P1)) as [_ [_ P3]].
  apply (P3 _ P2).
Qed.
    
Notation "m ₙx n" := (fun_val (multi_proto m) n) (at level 64, no associativity).

Lemma multi_zero: forall m, m ∈ ω -> m ₙx ₙ0 = ₙ0.
Proof.
  intros m P1.
  apply (multi_proto_elim_1 _ P1).
Qed.

Lemma multi_red: forall m n, m ∈ ω -> n ∈ ω -> m ₙx S(n) = m ₙ+ (m ₙx n).
Proof.
  intros m n P1 P2.
  apply (multi_proto_elim_2 _ _ P1 P2).
Qed.

Lemma multi_in_omega: forall m n, m ∈ ω -> n ∈ ω -> m ₙx n ∈ ω.
Proof.
  intros m n P1 P2.
  destruct (multi_proto_is_function _ P1) as [P3 [P4 P5]].
  apply P5.
  apply range_intro.
  exists n.
  apply fun_val_basic.
  + apply P3.
  + rewrite P4.
    apply P2.
Qed.

Lemma one_in_omega: ₙ1 ∈ ω.
Proof.
  apply (suc_in_omega _ empty_in_omega).
Qed.

Definition exp_proto (m: set) :=
  extract_set (recursion_theorem ω (ₙ1) (multi_proto m)).

Lemma exp_proto_is_function: forall m, m ∈ ω -> fun_maps (exp_proto m) ω ω.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω (ₙ1) (multi_proto m)) 
    (one_in_omega) (multi_proto_is_function _ P1)) as [P2 _].
  apply P2.
Qed.

Lemma exp_proto_elim_1: forall m, m ∈ ω -> fun_val (exp_proto m) ∅ = ₙ1.
Proof.
  intros m P1.
  destruct (extract_set_property (recursion_theorem ω (ₙ1) (multi_proto m)) 
    (one_in_omega) (multi_proto_is_function _ P1)) as [_ [P2 _]].
  apply P2.
Qed.

Lemma exp_proto_elim_2: forall m n, m ∈ ω -> n ∈ ω -> 
    fun_val (exp_proto m) (S(n)) = fun_val (multi_proto m) (fun_val (exp_proto m) n).
Proof.
  intros m n P1 P2.
  destruct (extract_set_property (recursion_theorem ω (ₙ1) (multi_proto m)) 
    (one_in_omega) (multi_proto_is_function _ P1)) as [_ [_ P3]].
  apply (P3 _ P2).
Qed.
    
Notation "m ₙ^ n" := (fun_val (exp_proto m) n) (at level 65, no associativity).

Lemma exp_zero: forall m, m ∈ ω -> m ₙ^ ₙ0 = ₙ1.
Proof.
  intros m P1.
  apply (exp_proto_elim_1 _ P1).
Qed.

Lemma exp_red: forall m n, m ∈ ω -> n ∈ ω -> m ₙ^ S(n) = m ₙx (m ₙ^ n).
Proof.
  intros m n P1 P2.
  apply (exp_proto_elim_2 _ _ P1 P2).
Qed.

Lemma add_zero_l: forall m, m ∈ ω -> ₙ0 ₙ+ m = m.
Proof.
  intros m P1.
  assert (ₙ0 ₙ+ ₙ0 = ₙ0) as P2.
  { apply (add_zero _ empty_in_omega). }
  assert (forall k, k ∈ ω -> ₙ0 ₙ+ k = k -> ₙ0 ₙ+ S(k) = S(k)) as P3.
  { intros k P3 P4.
    rewrite (add_red _ _ empty_in_omega P3).
    f_equal.
    apply P4. }
  apply (induction_principle _ P2 P3 _ P1).
Qed.

Lemma add_red_l: forall m n, m ∈ ω -> n ∈ ω -> S(m) ₙ+ n = S(m ₙ+ n).
Proof.
  intros m n P1 P2.
  assert (S(m) ₙ+ ₙ0 = S(m ₙ+ ₙ0)) as P3.
  { rewrite (add_zero _ (suc_in_omega _ P1)).
    rewrite (add_zero _ P1).
    reflexivity. }
  assert (forall k, k ∈ ω -> 
    S(m) ₙ+ k = S(m ₙ+ k) -> S(m) ₙ+ S(k) = S(m ₙ+ S(k))) as P4.
  { intros k P4 P5.
    rewrite (add_red _ _ (suc_in_omega _ P1) P4).
    rewrite P5.
    f_equal.
    symmetry.
    apply (add_red _ _ P1 P4). }
  apply (induction_principle _ P3 P4 _ P2).
Qed.

Lemma add_commutative: forall m n, m ∈ ω -> n ∈ ω -> m ₙ+ n = n ₙ+ m.
Proof. 
  intros m n P1 P2.
  assert (m ₙ+ ₙ0 = ₙ0 ₙ+ m) as P3.
  { rewrite (add_zero _ P1).
    rewrite (add_zero_l _ P1).
    reflexivity. }
  assert (forall k, k ∈ ω -> m ₙ+ k = k ₙ+ m -> m ₙ+ S(k) = S(k) ₙ+ m) as P4.
  { intros k P4 P5.
    rewrite (add_red _ _ P1 P4).
    rewrite (add_red_l _ _ P4 P1).
    f_equal.
    apply P5. }
  apply (induction_principle _ P3 P4 _ P2).
Qed.

Lemma add_associative: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->
  m ₙ+ (n ₙ+ p) = (m ₙ+ n) ₙ+ p.
Proof.
  intros m n p P1 P2 P3.
  assert (m ₙ+ (n ₙ+ ₙ0) = (m ₙ+ n) ₙ+ ₙ0) as P4.
  { rewrite (add_zero _ P2).
    symmetry.    
    apply add_zero.
    apply (add_in_omega _ _ P1 P2). }
  assert (forall k, k ∈ ω -> m ₙ+ (n ₙ+ k) = (m ₙ+ n) ₙ+ k ->
    m ₙ+ (n ₙ+ S(k)) = (m ₙ+ n) ₙ+ S(k)) as P5.
  { intros k P5 P6.
    rewrite (add_red _ _ (add_in_omega _ _ P1 P2) P5).
    rewrite <- P6.
    rewrite <- (add_red _ _ P1 (add_in_omega _ _ P2 P5)).
    rewrite <- (add_red _ _ P2 P5).
    reflexivity. }
  apply (induction_principle _ P4 P5 _ P3).
Qed.

Lemma multi_zero_l: forall m, m ∈ ω -> ₙ0 ₙx m = ₙ0.
Proof.
  intros m P1.
  assert (ₙ0 ₙx ₙ0 = ₙ0) as P2.
  { apply (multi_zero _ empty_in_omega). }
  assert (forall k, k ∈ ω -> ₙ0 ₙx k = ₙ0 -> ₙ0 ₙx S(k) = ₙ0) as P3.
  { intros k P3 P4.
    rewrite (multi_red _ _ empty_in_omega P3).
    rewrite P4.
    apply (add_zero _ empty_in_omega). }
  apply (induction_principle _ P2 P3 _ P1).
Qed.

Lemma multi_red_l: forall m n, m ∈ ω -> n ∈ ω -> S(m) ₙx n = n ₙ+ (m ₙx n).
Proof.
  intros m n P1 P2.
  assert (S(m) ₙx ₙ0 = ₙ0 ₙ+ (m ₙx ₙ0)) as P3.
  { rewrite (multi_zero _ (suc_in_omega _ P1)).
    rewrite (multi_zero _ P1).
    rewrite (add_zero _ empty_in_omega).
    reflexivity. }
  assert (forall k, k ∈ ω -> 
    S(m) ₙx k = k ₙ+ (m ₙx k) -> S(m) ₙx S(k) = S(k) ₙ+ (m ₙx S(k))) as P4.
  { intros k P4 P5.
    rewrite (multi_red _ _ (suc_in_omega _ P1) P4).
    rewrite (multi_red _ _ P1 P4).
    rewrite P5.
    rewrite (add_associative _ _ _ (suc_in_omega _ P1) P4 (multi_in_omega _ _ P1 P4)).
    rewrite (add_associative _ _ _ (suc_in_omega _ P4) P1 (multi_in_omega _ _ P1 P4)).
    rewrite (add_commutative _ _ (suc_in_omega _ P4) P1).
    rewrite (add_red _ _ P1 P4).
    rewrite (add_red_l _ _ P1 P4).
    reflexivity. }
  apply (induction_principle _ P3 P4 _ P2).
Qed.

Lemma distributive_l: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->
  m ₙx (n ₙ+ p) = m ₙx n ₙ+ m ₙx p.
Proof.
  intros m n p P1 P2 P3.
  assert (m ₙx (n ₙ+ ₙ0) = m ₙx n ₙ+ m ₙx ₙ0) as P4.
  { rewrite (add_zero _ P2).
    rewrite (multi_zero _ P1).
    rewrite (add_zero _ (multi_in_omega _ _ P1 P2)). 
    reflexivity. }
  assert (forall k, k ∈ ω -> m ₙx (n ₙ+ k) = m ₙx n ₙ+ m ₙx k -> 
    m ₙx (n ₙ+ S(k)) = m ₙx n ₙ+ m ₙx S(k)) as P5.
  { intros k P5 P6.
    rewrite (add_red _ _ P2 P5).
    rewrite (multi_red _ _ P1 (add_in_omega _ _ P2 P5)).
    rewrite P6.
    rewrite (multi_red _ _ P1 P5).
    rewrite (add_associative _ _ _ 
      (multi_in_omega _ _ P1 P2) P1 (multi_in_omega _ _ P1 P5)).
    rewrite (add_commutative _ _ (multi_in_omega _ _ P1 P2) P1).
    rewrite <- (add_associative _ _ _ 
      P1 (multi_in_omega _ _ P1 P2) (multi_in_omega _ _ P1 P5)).
    reflexivity. }
  apply (induction_principle _ P4 P5 _ P3).
Qed.

Lemma multi_commutative: forall m n, m ∈ ω -> n ∈ ω -> m ₙx n = n ₙx m.
Proof.
  intros m n P1 P2.
  assert (m ₙx ₙ0 = ₙ0 ₙx m) as P3.
  { rewrite (multi_zero _ P1).
    rewrite (multi_zero_l _ P1).
    reflexivity. }
  assert (forall k, k ∈ ω -> m ₙx k = k ₙx m -> m ₙx S(k) = S(k) ₙx m) as P4.
  { intros k P4 P5.
    rewrite (multi_red _ _ P1 P4).
    rewrite (multi_red_l _ _ P4 P1).
    f_equal.
    apply P5. }
  apply (induction_principle _ P3 P4 _ P2).
Qed.

Lemma multi_associative: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->
  m ₙx (n ₙx p) = (m ₙx n) ₙx p.
Proof.
  intros m n p P1 P2 P3.
  assert (m ₙx (n ₙx ₙ0) = (m ₙx n) ₙx ₙ0) as P4.
  { rewrite (multi_zero _ P2).
    rewrite (multi_zero _ P1).
    rewrite (multi_zero _ (multi_in_omega _ _ P1 P2)).
    reflexivity. }
  assert (forall k, k ∈ ω -> m ₙx (n ₙx k) = (m ₙx n) ₙx k ->
    m ₙx (n ₙx S(k)) = (m ₙx n) ₙx S(k)) as P5.
  { intros k P5 P6.
    rewrite (multi_red _ _ (multi_in_omega _ _ P1 P2) P5).
    rewrite <- P6.
    rewrite (multi_red _ _ P2 P5). 
    rewrite (distributive_l _ _ _ P1 P2 (multi_in_omega _ _ P2 P5)).
    reflexivity. }
  apply (induction_principle _ P4 P5 _ P3).
Qed.

Lemma multi_equal_zero: forall m n, m ∈ ω -> n ∈ ω ->
  m ₙx n = ₙ0 -> m = ₙ0 \/ n = ₙ0.
Proof.
  intros m n P1 P2.
  apply contraposition4.
  intros P3 P4.
  destruct (not_or_and _ _ P3) as [P5 P6].
  destruct (nat_is_suc _ P1 P5) as [mm [P7 P8]].
  destruct (nat_is_suc _ P2 P6) as [nn [P9 P10]].
  rewrite P8 in P4.
  rewrite (multi_red_l _ _ P7 P2) in P4.
  rewrite P10 in P4.
  rewrite (add_red_l _ _ P9 (multi_in_omega _ _ P7 (suc_in_omega _ P9))) in P4.
  absurd (ₙ0 = S( nn ₙ+ mm ₙx S( nn))).
  + apply empty_not_suc.
  + symmetry.
    apply P4.
Qed.

Definition less (m: set) (n: set) := m ∈ n.
Notation "m ₙ< n" := (less m n) (at level 65, no associativity).

Definition less_equal (m: set) (n: set) := (less m n) \/ (m = n).
Notation "m ₙ≤ n" := (less_equal m n) (at level 65, no associativity).

Lemma in_suc: forall m n, nat n -> m ∈ S(n) -> m ∈ n \/ m = n.
Proof.
  intros m n P2 P3.
  destruct (in_union2_in _ _ _ P3) as [P4|P4].
  + left.
    apply P4.
  + right.
    symmetry.   
    apply (in_singleton_equal _ _ P4).
Qed.

Lemma in_nat_nat: forall m n, nat n -> m ∈ n -> nat m.
Proof.
  intros m n P1 P2.
  assert (forall m1, m1 ∈ ₙ0 -> nat m1) as P3.
  { intros m1 Q1.
    absurd (m1 ∈ ₙ0).
    + apply not_in_empty.
    + apply Q1. }
  assert (forall k, k ∈ ω -> (forall m1, m1 ∈ k -> nat m1) -> 
    (forall m1, m1 ∈ S(k) -> nat m1)) as P4.
  { intros k Q1 Q2 m1 Q3.
    destruct (in_suc _ _ (omega_elim _ Q1) Q3) as [Q4|Q4].
    + apply (Q2 _ Q4).
    + rewrite Q4.
      apply (omega_elim _ Q1). }
  apply (induction_principle _ P3 P4 _ (omega_intro _ P1) _ P2).
Qed.

Lemma suc_less: forall m n, nat m -> nat n -> m ₙ< n -> S(m) ₙ< S(n).
Proof.
  intros m n P1 P2 P3.
  assert (forall m, m ₙ< ₙ0 -> S(m) ₙ< S(ₙ0)) as P4.
  { intros m1 Q1.
    absurd (m1 ₙ< ₙ0).
    + apply not_in_empty.
    + apply Q1. }
  assert (forall k, k ∈ ω -> (forall m1, m1 ₙ< k -> S(m1) ₙ< S(k)) ->
    (forall m2, m2 ₙ< S(k) -> S(m2) ₙ< S(S(k)))) as P5.
  { intros k Q1 Q2 m2 Q3.
    destruct (in_suc _ _ (omega_elim _ Q1) Q3) as [Q4|Q4].
    + pose (nat_is_trans _ (suc_is_nat _ (suc_is_nat _ (omega_elim _ Q1)))) as Q5.
      apply (Q5 _ _ (conj (Q2 _ Q4) (suc_intro_1 (S(k))))).
    + rewrite Q4.
      apply suc_intro_1. }
  apply (induction_principle _ P4 P5 _ (omega_intro _ P2) _ P3).
Qed.

Lemma empty_in_nat: forall n, nat n -> n <> ₙ0 -> ₙ0 ∈ n.
Proof.
  intros n P1 P2.
  pose (fun k => nat k -> k <> ₙ0 -> ₙ0 ∈ k) as P.
  assert (P (ₙ0)) as P3.
  { intros Q1 Q2.
    contradiction. }
  assert (forall k, k ∈ ω -> P k -> P (S(k))) as P4.
  { intros k Q1 Q2 Q3 Q4.
    destruct (LEM (k = ₙ0)) as [Q5|Q5].
    + rewrite Q5.
      apply suc_intro_1.
    + pose (nat_is_trans _ (suc_is_nat _ (omega_elim _ Q1))) as Q6.
      apply (Q6 _ _ (conj (Q2 (omega_elim _ Q1) Q5) (suc_intro_1 k))). }
  apply (induction_principle _ P3 P4 _ (omega_intro _ P1) P1 P2).
Qed.
    
Theorem trichotomy_of_nat: forall m n, nat m -> nat n ->
  ((m ₙ< n) /\ ~(m = n) /\ ~(n ₙ< m)) \/
  (~(m ₙ< n) /\ (m = n) /\ ~(n ₙ< m)) \/
  (~(m ₙ< n) /\ ~(m = n) /\ (n ₙ< m)).
Proof.
  intros m n P1 P2.
  pose (fun k => nat k -> k ∈ n \/ k = n \/ n ∈ k) as P.
  assert (P (ₙ0)) as P3.
  { intros Q1.
    destruct (LEM (n = ₙ0)) as [Q2|Q2].
    + right. left.
      symmetry.
      apply Q2.
    + left.
      apply (empty_in_nat _ P2 Q2). }
  assert (forall k, k ∈ ω -> P k -> P (S(k))) as P4.
  { intros k Q1 Q2 Q3.
    pose (in_nat_nat _ _ Q3 (suc_intro_1 k)) as Q4.
    destruct (Q2 Q4) as [Q5|[Q5|Q5]].
    + destruct (suc_elim _ _ (suc_less _ _ Q4 P2 Q5)) as [Q6|Q6].
      - right. left.
        apply Q6.
      - left.
        apply Q6.
    + right. right.
      rewrite Q5.
      apply suc_intro_1.
    + right. right.
      apply (nat_is_trans _ Q3 _ _ (conj Q5 (suc_intro_1 k))). }
  destruct (induction_principle _ P3 P4 _ (omega_intro _ P1) P1) as [P5|[P5|P5]].
  + left.
    split.
    { apply P5. }
    split.
    { intros P6.
      rewrite P6 in P5.
      absurd (n ∈ n).
      + apply (nat_not_in_self _ (omega_intro _ P2)).
      + apply P5. }
    { intros P6.
      absurd (n ∈ n).
      + apply (nat_not_in_self _ (omega_intro _ P2)).
      + apply (nat_is_trans _ P2 _ _ (conj P6 P5)). }
  + right. left.
    split. 
    { rewrite P5.
      apply (nat_not_in_self _ (omega_intro _ P2)). }
    split.
    { apply P5. }
    { rewrite P5.
      apply (nat_not_in_self _ (omega_intro _ P2)). }
  + right. right.
    split.
    { intros P6.
      absurd (n ∈ n).
      + apply (nat_not_in_self _ (omega_intro _ P2)).
      + apply (nat_is_trans _ P2 _ _ (conj P5 P6)). }
    split.
    { intros P6.
      rewrite P6 in P5.
      absurd (n ∈ n).
      + apply (nat_not_in_self _ (omega_intro _ P2)).
      + apply P5. }
    { apply P5. }
Qed.

Theorem trichotomy_of_nat_weak: forall m n, nat m -> nat n ->
  (m ₙ< n) \/ (m = n) \/ (n ₙ< m).
Proof. 
  intros m n P1 P2.
  destruct (trichotomy_of_nat _ _ P1 P2) as [[P3 _]|[[_ [P3 _]]|[_ [_ P3]]]]. 
  + left. 
    apply P3.
  + right. left.
    apply P3.
  + right. right.
    apply P3.
Qed.
