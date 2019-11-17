Require Import logic.
Require Import axiom.
Require Import basic.
Require Import relation.

Lemma successor_elim: forall A x, x ∈ S(A) -> x = A \/ x ∈ A.
Proof.
  intros A x P1.
  destruct (in_union2_in _ _ _ P1) as [P2|P2].
  + right.
    apply P2.
  + left.
    symmetry.
    apply (in_singleton_equal _ _ P2).
Qed.

Lemma successor_intro_1: forall A, A ∈ S(A).
Proof.
  intros A.
  apply in_in_union2_2.
  apply in_singleton.
Qed.

Lemma successor_intro_2: forall A x, x ∈ A -> x ∈ S(A).
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
Notation "0ₙ" := ∅ (at level 60, no associativity).
Notation "1ₙ" := (S(∅)).
Notation "2ₙ" := (S(S(∅))).
Notation "3ₙ" := (S(S(S(∅)))).
Notation "4ₙ" := (S(S(S(S(∅))))).

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

Lemma successor_in_omega: forall k, k ∈ ω -> S(k) ∈ ω.
Proof.
  intros k P1.
  apply omega_intro.
  intros B P2.
  pose ((omega_elim _ P1) B P2) as P3.
  destruct P2 as [P2 P4].
  apply (P4 _ P3).
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
      apply (subset_intro _ _ _ (successor_in_omega _ P6) (P2 _ P6 P7)). }
  rewrite <- (induction_principle_ _ P4 P5) in P3.
  destruct (subset_elim _ _ _ P3) as [_ P6].
  apply P6.
Qed.
    
Lemma nat_is_successor: forall x, x ∈ ω -> x <> ∅ -> exists y, x = S(y).
Proof.
  intros x P1 P2.
  pose (P := fun x => x = ∅ \/ exists y, x = S(y)).
  assert (P ∅) as P3.
  { left.
    reflexivity. }
  assert (forall k, k ∈ ω -> P k -> P (S(k))) as P4.
  { intros k _ [P4|P4].
    + right.
      exists ∅.
      rewrite P4.
      reflexivity.
    + right.
      exists k.
      reflexivity. }
  destruct (induction_principle _ P3 P4 x P1) as [P5|P5].
  + contradiction.
  + apply P5.
Qed.

Lemma empty_not_successor: forall x, ∅ <> S(x).
Proof.
  intros x P1.
  absurd (x ∈ ∅).
  + apply not_in_empty.
  + rewrite P1.
    apply successor_intro_1.
Qed.
    
(* Skip Peano's System *)
Definition σ := subset_ctor (fun x => exists y, x = ⟨y, S(y)⟩) (cp ω ω).

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

Lemma union_trans_successor: forall A, trans A -> ∪(S(A)) = A.
Proof.
  intros A P1.
  apply ax_exten.
  intros x.
  split.
  + intros P2.
    destruct (in_union_in _ _ P2) as [y [P3 P4]].
    destruct (successor_elim _ _ P3) as [P5|P5].
    - rewrite <- P5.
      apply P4.
    - apply (P1 _ _ (conj P4 P5)).
  + intros P2.
    apply (in_in_union).
    exists A.
    split.
    - apply successor_intro_1.
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
    rewrite (union_trans_successor _ P3).
    intros x P4.
    apply (successor_intro_2 _ _ P4). }
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
    destruct (successor_elim _ _ P4) as [P5|P5].
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
    + destruct (successor_elim _ _ P5) as [P6|P6].
      - pose (P7 := successor_intro_1 k).
        rewrite P6 in P7.
        apply P7.
      - pose (P7 := successor_intro_1 k).
        apply (nat_is_trans _ (omega_elim _ P3) _ _ (conj P7 P6)). }
  apply (induction_principle _ P2 P3 _ P1).
Qed.

Lemma successor_unique: forall x y, x ∈ ω -> y ∈ ω -> S(x) = S(y) -> x = y.
Proof. 
  intros x y P1 P2 P3.
  pose (successor_intro_1 x) as P4.
  rewrite P3 in P4.
  destruct (successor_elim _ _ P4) as [P5|P5].
  + apply P5.
  + pose (successor_intro_1 y) as P6.
    rewrite <- P3 in P6.
    destruct (successor_elim _ _ P6) as [P7|P7].
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
    + apply empty_not_successor.
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
      - apply (successor_in_omega _ P5).
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
      apply (successor_in_omega _ P5). }
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
        rewrite <- (successor_unique _ _ P5 Q1 (in_singleton_equal _ _ Q3)).
        apply domain_intro.
        exists y.
        apply P4. 
      - assert (x = n) as QQ. 
        { rewrite single_value_domain in Q3.
          apply (successor_unique _ _ P5 Q1 (in_singleton_equal _ _ Q3)). }
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

Theorem recursion_theorem: forall A a F, a ∈ A -> fun_maps F A A ->
  exists h, fun_maps h ω A /\ (fun_val h ∅) = a /\ 
    (forall n, n ∈ ω -> fun_val h (S(n)) = fun_val F (fun_val h n)).
Proof.
  intros A a F P1 P2.
  pose (P := _rec_accept F A a).
  pose (H := subset_ctor P (𝒫(cp ω A))).
  pose (h := ∪(H)).
  exists h.
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
    { pose (successor_in_omega _ P3) as P4.
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


