Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Inductive.
Require Import Nat.Nature.
Require Import Nat.Recursion.

(*Require dpdgraph.dpdgraph.*)

Definition nat0 := (∅).
Definition nat1 := (S(nat0)).
Definition nat2 := (S(nat1)).
Notation "'〇ₙ'" := (nat0).
Notation "'一ₙ'" := (nat1).
Notation "'二ₙ'" := (nat2).

Notation σ := {x: ω ⨉ ω| ∃ y, x = ⟨y, S(y)⟩}.

Definition add_proto (m: J) := (ex_outl (recursion_thm ω m σ)).
Definition mul_proto (m: J) := (ex_outl (recursion_thm ω (〇ₙ) (add_proto m))).
Definition exp_proto (m: J) := (ex_outl (recursion_thm ω (一ₙ) (mul_proto m))).

Notation "m +ₙ n" := ((add_proto m)[n]).
Notation "m ×ₙ n" := ((mul_proto m)[n]).
Notation "m ^ₙ n" := ((exp_proto m)[n]).

(* Sigma *)
Lemma sigma_is_fn: fn σ.
Proof.
  split.
  + apply cp_sub_rel.
  + intros a b1 b2 P1 P2.
    destruct (sub_e _ _ _ P1) as [_ [y1 P3]].
    destruct (opair_eq_e _ _ _ _ P3) as [P4 P5].
    apply (eq_t P5).
    apply (eq_cl (λ x, S(x) = b2) P4).
    destruct (sub_e _ _ _ P2) as [_ [y2 P6]].
    destruct (opair_eq_e _ _ _ _ P6) as [P7 P8].
    apply (eq_cr (λ x, S(a) = x) P8).
    apply (eq_cr (λ x, S(x) = S(y2)) P7).
    apply eq_r.
Qed.

Lemma sigma_dom: dom(σ) = ω.
Proof.
  apply sub_a.
  split.
  * intros x P1.
    destruct (dom_e _ _ P1) as [y P2].
    destruct (sub_e _ _ _ P2) as [P3 _].
    destruct (cp_e2 _ _ _ _ P3) as [P4 _].
    apply P4.
  * intros x P2.
    apply dom_i.
    exists (S(x)).
    apply sub_i.
    + apply cp_i.
      - apply P2.
      - apply (suc_is_nat _ P2).
    + exists x.
      apply eq_r.
Qed.

Lemma sigma_ran: ran(σ) ⊆ ω.
Proof.
  intros y P1.
  destruct (ran_e _ _ P1) as [x P2].
  destruct (sub_e _ _ _ P2) as [P3 _].
  destruct (cp_e2 _ _ _ _ P3) as [_ P4]. 
  apply P4.
Qed.

Lemma sigma_fnm: fnm σ ω ω.
Proof.
  split.
  + apply sigma_is_fn.
  + split.
    - apply sigma_dom.
    - apply sigma_ran.
Qed.

Lemma sigma_i: ∀ k, k ∈ ω → S(k) = σ[k].
Proof.
  intros k P1.
  apply fval_i.
  + apply sigma_is_fn.
  + apply sub_i.
    - apply cp_i.
      * apply P1.
      * apply (suc_is_nat _ P1).
    - exists k.
      apply eq_r.
Qed.

(* Addition *)
Lemma add_proto_is_fn: ∀ m, m ∈ ω → fnm (add_proto m) ω ω.
Proof.
  intros m P1.
  destruct (ex_outr (recursion_thm ω m σ) P1 sigma_fnm) as [P2 _].
  apply P2.
Qed.

Lemma add_proto_e1: ∀ m, m ∈ ω → (add_proto m)[∅] = m.
Proof.
  intros m P1.
  destruct (ex_outr (recursion_thm ω m σ) P1 sigma_fnm) as [_ [P2 _]].
  apply P2.
Qed.

Lemma add_proto_e2: ∀ m, ∀ n, m ∈ ω → n ∈ ω → (add_proto m)[S(n)] = S((add_proto m)[n]).
Proof.
  intros m n P1 P2.
  destruct (ex_outr (recursion_thm ω m σ) P1 sigma_fnm) as [[P3 [P4 P5]] [_ P6]].
  apply (eq_cr (λ x, x = S(m +ₙ n)) (P6 _ P2)).
  apply eq_s.
  apply sigma_i.
  apply P5.
  apply (fval_ran _ _ P3).
  apply (eq_cr (λ x, n ∈ x) P4).
  apply P2.
Qed.
 
Lemma zero_is_nat: 〇ₙ ∈ ω.
Proof.
  apply empty_is_nat.
Qed.

Lemma one_is_nat: 一ₙ ∈ ω.
Proof.
  apply (suc_is_nat _ zero_is_nat).
Qed.

Lemma add_zero: ∀ m, m ∈ ω → m +ₙ 〇ₙ = m.
Proof.
  intros m P1.
  apply (add_proto_e1 _ P1).
Qed.

Lemma add_red: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m +ₙ S(n) = S(m +ₙ n).
Proof.
  intros m n P1 P2.
  apply (add_proto_e2 _ _ P1 P2).
Qed.

Lemma add_is_nat: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m +ₙ n ∈ ω.
Proof.
  intros m n P1 P2.
  destruct (add_proto_is_fn _ P1) as [P3 [P4 P5]].
  apply P5.
  apply ran_i.
  exists n.
  apply fval_i2.
  + apply P3.
  + apply (eq_cr (λ x, n ∈ x) P4).
    apply P2.
Qed.

Theorem one_one_two: 一ₙ +ₙ 一ₙ = 二ₙ.
Proof.
  apply (eq_cr (λ x, x = 二ₙ) (add_red (一ₙ) (〇ₙ) one_is_nat zero_is_nat)).
  apply (eq_cr (λ x, S(x) = 二ₙ) (add_zero (一ₙ) one_is_nat)).
  apply eq_r.
Qed.
(*----------------------------------------------------------------------------*)

(* Multiplication *)
Lemma mul_proto_is_fn: ∀ m, m ∈ ω → fnm (mul_proto m) ω ω.
Proof.
  intros m P1.
  destruct (ex_outr (recursion_thm ω (〇ₙ) (add_proto m)) 
    (zero_is_nat) (add_proto_is_fn _ P1)) as [P2 _].
  apply P2.
Qed.

Lemma mul_proto_e1: ∀ m, m ∈ ω → (mul_proto m)[〇ₙ] = 〇ₙ.
Proof.
  intros m P1.
  destruct (ex_outr (recursion_thm ω (〇ₙ) (add_proto m)) 
    (zero_is_nat) (add_proto_is_fn _ P1)) as [_ [P2 _]].
  apply P2.
Qed.

Lemma mul_proto_e2: ∀ m, ∀ n, m ∈ ω → n ∈ ω → 
    (mul_proto m)[S(n)] = (add_proto m)[(mul_proto m)[n]].
Proof.
  intros m n P1 P2.
  destruct (ex_outr (recursion_thm ω (〇ₙ) (add_proto m)) 
    (zero_is_nat) (add_proto_is_fn _ P1)) as [_ [_ P3]].
  apply (P3 _ P2).
Qed. 

Lemma mul_zero: ∀ m, m ∈ ω → m ×ₙ 〇ₙ = 〇ₙ.
Proof.
  intros m P1.
  apply (mul_proto_e1 _ P1).
Qed.

Lemma mul_red: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m ×ₙ S(n) = m +ₙ (m ×ₙ n).
Proof.
  intros m n P1 P2.
  apply (mul_proto_e2 _ _ P1 P2).
Qed.

Lemma mul_one: ∀ m, m ∈ ω → m ×ₙ 一ₙ = m.
Proof.
  intros m P1.
  apply (eq_cr (λ x, x = m) (mul_red _ _ P1 zero_is_nat)).
  apply (eq_cr (λ x, m +ₙ x = m) (mul_zero _ P1)).
  apply (eq_cr (λ x, x = m) (add_zero _ P1)).
  apply eq_r.
Qed.

Lemma mul_is_nat: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m ×ₙ n ∈ ω.
Proof.
  intros m n P1 P2.
  destruct (mul_proto_is_fn _ P1) as [P3 [P4 P5]].
  apply P5.
  apply ran_i.
  exists n.
  apply fval_i2.
  + apply P3.
  + apply (eq_cr (λ x, n ∈ x) P4).
    apply P2.
Qed.
(*----------------------------------------------------------------------------*)

(* Exponential *)
Lemma exp_proto_is_fn: ∀ m, m ∈ ω → fnm (exp_proto m) ω ω.
Proof.
  intros m P1.
  destruct (ex_outr (recursion_thm ω (一ₙ) (mul_proto m)) 
    one_is_nat (mul_proto_is_fn _ P1)) as [P2 _].
  apply P2.
Qed.

Lemma exp_proto_e1: ∀ m, m ∈ ω → (exp_proto m)[〇ₙ] = 一ₙ.
Proof.
  intros m P1.
  destruct (ex_outr (recursion_thm ω (一ₙ) (mul_proto m)) 
    one_is_nat (mul_proto_is_fn _ P1)) as [_ [P2 _]].
  apply P2.
Qed.

Lemma exp_proto_e2: ∀ m, ∀ n, m ∈ ω → n ∈ ω → 
    (exp_proto m)[S(n)] = (mul_proto m)[(exp_proto m)[n]].
Proof.
  intros m n P1 P2.
  destruct (ex_outr (recursion_thm ω (一ₙ) (mul_proto m)) 
    one_is_nat (mul_proto_is_fn _ P1)) as [_ [_ P3]].
  apply (P3 _ P2).
Qed.

Lemma exp_zero: ∀ m, m ∈ ω → m ^ₙ 〇ₙ = 一ₙ.
Proof.
  intros m P1.
  apply (exp_proto_e1 _ P1).
Qed.

Lemma exp_red: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m ^ₙ S(n) = m ×ₙ (m ^ₙ n).
Proof.
  intros m n P1 P2.
  apply (exp_proto_e2 _ _ P1 P2).
Qed.
(*----------------------------------------------------------------------------*)

(*[> Arith Law <]*)
(*Lemma add_zero_l: forall m, m ∈ ω -> n.0 +ₙ m = m.*)
(*Proof.*)
  (*intros m P1.*)
  (*assert (n.0 +ₙ n.0 = n.0) as P2.*)
  (*{ apply (add_zero _ empty_is_nat). }*)
  (*assert (forall k, k ∈ ω -> n.0 +ₙ k = k -> n.0 +ₙ S(k) = S(k)) as P3.*)
  (*{ intros k P3 P4.*)
    (*rewrite (add_red _ _ empty_is_nat P3).*)
    (*f_equal.*)
    (*apply P4. }*)
  (*apply (induction_principle _ P2 P3 _ P1).*)
(*Qed.*)

(*Lemma add_red_l: forall m n, m ∈ ω -> n ∈ ω -> S(m) +ₙ n = S(m +ₙ n).*)
(*Proof.*)
  (*intros m n P1 P2.*)
  (*assert (S(m) +ₙ n.0 = S(m +ₙ n.0)) as P3.*)
  (*{ rewrite (add_zero _ (suc_is_nat _ P1)).*)
    (*rewrite (add_zero _ P1).*)
    (*reflexivity. }*)
  (*assert (forall k, k ∈ ω -> *)
    (*S(m) +ₙ k = S(m +ₙ k) -> S(m) +ₙ S(k) = S(m +ₙ S(k))) as P4.*)
  (*{ intros k P4 P5.*)
    (*rewrite (add_red _ _ (suc_is_nat _ P1) P4).*)
    (*rewrite P5.*)
    (*f_equal.*)
    (*symmetry.*)
    (*apply (add_red _ _ P1 P4). }*)
  (*apply (induction_principle _ P3 P4 _ P2).*)
(*Qed.*)

(*Lemma add_commutative: forall m n, m ∈ ω -> n ∈ ω -> m +ₙ n = n +ₙ m.*)
(*Proof. *)
  (*intros m n P1 P2.*)
  (*assert (m +ₙ n.0 = n.0 +ₙ m) as P3.*)
  (*{ rewrite (add_zero _ P1).*)
    (*rewrite (add_zero_l _ P1).*)
    (*reflexivity. }*)
  (*assert (forall k, k ∈ ω -> m +ₙ k = k +ₙ m -> m +ₙ S(k) = S(k) +ₙ m) as P4.*)
  (*{ intros k P4 P5.*)
    (*rewrite (add_red _ _ P1 P4).*)
    (*rewrite (add_red_l _ _ P4 P1).*)
    (*f_equal.*)
    (*apply P5. }*)
  (*apply (induction_principle _ P3 P4 _ P2).*)
(*Qed.*)

(*Lemma add_associative: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->*)
  (*m +ₙ (n +ₙ p) = (m +ₙ n) +ₙ p.*)
(*Proof.*)
  (*intros m n p P1 P2 P3.*)
  (*assert (m +ₙ (n +ₙ n.0) = (m +ₙ n) +ₙ n.0) as P4.*)
  (*{ rewrite (add_zero _ P2).*)
    (*symmetry.    *)
    (*apply add_zero.*)
    (*apply (add_is_nat _ _ P1 P2). }*)
  (*assert (forall k, k ∈ ω -> m +ₙ (n +ₙ k) = (m +ₙ n) +ₙ k ->*)
    (*m +ₙ (n +ₙ S(k)) = (m +ₙ n) +ₙ S(k)) as P5.*)
  (*{ intros k P5 P6.*)
    (*rewrite (add_red _ _ (add_is_nat _ _ P1 P2) P5).*)
    (*rewrite <- P6.*)
    (*rewrite <- (add_red _ _ P1 (add_is_nat _ _ P2 P5)).*)
    (*rewrite <- (add_red _ _ P2 P5).*)
    (*reflexivity. }*)
  (*apply (induction_principle _ P4 P5 _ P3).*)
(*Qed.*)

(*Lemma mul_zero_l: forall m, m ∈ ω -> n.0 ×ₙ m = n.0.*)
(*Proof.*)
  (*intros m P1.*)
  (*assert (n.0 ×ₙ n.0 = n.0) as P2.*)
  (*{ apply (mul_zero _ empty_is_nat). }*)
  (*assert (forall k, k ∈ ω -> n.0 ×ₙ k = n.0 -> n.0 ×ₙ S(k) = n.0) as P3.*)
  (*{ intros k P3 P4.*)
    (*rewrite (mul_red _ _ empty_is_nat P3).*)
    (*rewrite P4.*)
    (*apply (add_zero _ empty_is_nat). }*)
  (*apply (induction_principle _ P2 P3 _ P1).*)
(*Qed.*)

(*Lemma mul_red_l: forall m n, m ∈ ω -> n ∈ ω -> S(m) ×ₙ n = n +ₙ (m ×ₙ n).*)
(*Proof.*)
  (*intros m n P1 P2.*)
  (*assert (S(m) ×ₙ n.0 = n.0 +ₙ (m ×ₙ n.0)) as P3.*)
  (*{ rewrite (mul_zero _ (suc_is_nat _ P1)).*)
    (*rewrite (mul_zero _ P1).*)
    (*rewrite (add_zero _ empty_is_nat).*)
    (*reflexivity. }*)
  (*assert (forall k, k ∈ ω -> *)
    (*S(m) ×ₙ k = k +ₙ (m ×ₙ k) -> S(m) ×ₙ S(k) = S(k) +ₙ (m ×ₙ S(k))) as P4.*)
  (*{ intros k P4 P5.*)
    (*rewrite (mul_red _ _ (suc_is_nat _ P1) P4).*)
    (*rewrite (mul_red _ _ P1 P4).*)
    (*rewrite P5.*)
    (*rewrite (add_associative _ _ _ (suc_is_nat _ P1) P4 (mul_is_nat _ _ P1 P4)).*)
    (*rewrite (add_associative _ _ _ (suc_is_nat _ P4) P1 (mul_is_nat _ _ P1 P4)).*)
    (*rewrite (add_commutative _ _ (suc_is_nat _ P4) P1).*)
    (*rewrite (add_red _ _ P1 P4).*)
    (*rewrite (add_red_l _ _ P1 P4).*)
    (*reflexivity. }*)
  (*apply (induction_principle _ P3 P4 _ P2).*)
(*Qed.*)

(*Lemma distributive_l: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->*)
  (*m ×ₙ (n +ₙ p) = m ×ₙ n +ₙ m ×ₙ p.*)
(*Proof.*)
  (*intros m n p P1 P2 P3.*)
  (*assert (m ×ₙ (n +ₙ n.0) = m ×ₙ n +ₙ m ×ₙ n.0) as P4.*)
  (*{ rewrite (add_zero _ P2).*)
    (*rewrite (mul_zero _ P1).*)
    (*rewrite (add_zero _ (mul_is_nat _ _ P1 P2)). *)
    (*reflexivity. }*)
  (*assert (forall k, k ∈ ω -> m ×ₙ (n +ₙ k) = m ×ₙ n +ₙ m ×ₙ k -> *)
    (*m ×ₙ (n +ₙ S(k)) = m ×ₙ n +ₙ m ×ₙ S(k)) as P5.*)
  (*{ intros k P5 P6.*)
    (*rewrite (add_red _ _ P2 P5).*)
    (*rewrite (mul_red _ _ P1 (add_is_nat _ _ P2 P5)).*)
    (*rewrite P6.*)
    (*rewrite (mul_red _ _ P1 P5).*)
    (*rewrite (add_associative _ _ _ *)
      (*(mul_is_nat _ _ P1 P2) P1 (mul_is_nat _ _ P1 P5)).*)
    (*rewrite (add_commutative _ _ (mul_is_nat _ _ P1 P2) P1).*)
    (*rewrite <- (add_associative _ _ _ *)
      (*P1 (mul_is_nat _ _ P1 P2) (mul_is_nat _ _ P1 P5)).*)
    (*reflexivity. }*)
  (*apply (induction_principle _ P4 P5 _ P3).*)
(*Qed.*)

(*Lemma mul_commutative: forall m n, m ∈ ω -> n ∈ ω -> m ×ₙ n = n ×ₙ m.*)
(*Proof.*)
  (*intros m n P1 P2.*)
  (*assert (m ×ₙ n.0 = n.0 ×ₙ m) as P3.*)
  (*{ rewrite (mul_zero _ P1).*)
    (*rewrite (mul_zero_l _ P1).*)
    (*reflexivity. }*)
  (*assert (forall k, k ∈ ω -> m ×ₙ k = k ×ₙ m -> m ×ₙ S(k) = S(k) ×ₙ m) as P4.*)
  (*{ intros k P4 P5.*)
    (*rewrite (mul_red _ _ P1 P4).*)
    (*rewrite (mul_red_l _ _ P4 P1).*)
    (*f_equal.*)
    (*apply P5. }*)
  (*apply (induction_principle _ P3 P4 _ P2).*)
(*Qed.*)

(*Lemma mul_associative: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->*)
  (*m ×ₙ (n ×ₙ p) = (m ×ₙ n) ×ₙ p.*)
(*Proof.*)
  (*intros m n p P1 P2 P3.*)
  (*assert (m ×ₙ (n ×ₙ n.0) = (m ×ₙ n) ×ₙ n.0) as P4.*)
  (*{ rewrite (mul_zero _ P2).*)
    (*rewrite (mul_zero _ P1).*)
    (*rewrite (mul_zero _ (mul_is_nat _ _ P1 P2)).*)
    (*reflexivity. }*)
  (*assert (forall k, k ∈ ω -> m ×ₙ (n ×ₙ k) = (m ×ₙ n) ×ₙ k ->*)
    (*m ×ₙ (n ×ₙ S(k)) = (m ×ₙ n) ×ₙ S(k)) as P5.*)
  (*{ intros k P5 P6.*)
    (*rewrite (mul_red _ _ (mul_is_nat _ _ P1 P2) P5).*)
    (*rewrite <- P6.*)
    (*rewrite (mul_red _ _ P2 P5). *)
    (*rewrite (distributive_l _ _ _ P1 P2 (mul_is_nat _ _ P2 P5)).*)
    (*reflexivity. }*)
  (*apply (induction_principle _ P4 P5 _ P3).*)
(*Qed.*)

(*Lemma mul_equal_zero: forall m n, m ∈ ω -> n ∈ ω ->*)
  (*m ×ₙ n = n.0 -> m = n.0 \/ n = n.0.*)
(*Proof.*)
  (*intros m n P1 P2.*)
  (*apply contraposition4.*)
  (*intros P3 P4.*)
  (*destruct (not_or_and _ _ P3) as [P5 P6].*)
  (*destruct (nat_is_suc _ P1 P5) as [mm [P7 P8]].*)
  (*destruct (nat_is_suc _ P2 P6) as [nn [P9 P10]].*)
  (*rewrite P8 in P4.*)
  (*rewrite (mul_red_l _ _ P7 P2) in P4.*)
  (*rewrite P10 in P4.*)
  (*rewrite (add_red_l _ _ P9 (mul_is_nat _ _ P7 (suc_is_nat _ P9))) in P4.*)
  (*absurd (n.0 = S( nn +ₙ mm ×ₙ S( nn))).*)
  (*+ apply empty_not_suc.*)
  (*+ symmetry.*)
    (*apply P4.*)
(*Qed.*)

(*Lemma distributive_r: forall m n p, m ∈ ω -> n ∈ ω -> p ∈ ω ->*)
  (*(m +ₙ n) ×ₙ p = m ×ₙ p +ₙ n ×ₙ p.*)
(*Proof.*)
  (*intros m n p P1 P2 P3.*)
  (*rewrite (mul_commutative _ _ (add_is_nat _ _ P1 P2) P3).*)
  (*rewrite (mul_commutative _ _ P1 P3).*)
  (*rewrite (mul_commutative _ _ P2 P3).*)
  (*apply (distributive_l _ _ _ P3 P1 P2).*)
(*Qed.*)

(*Lemma add_equation: forall a b c d, a = b -> c = d -> a +ₙ c = b +ₙ d.*)
(*Proof.*)
  (*intros a b c d P1 P2.*)
  (*rewrite P1.*)
  (*rewrite P2.*)
  (*reflexivity.*)
(*Qed.*)

(*Lemma add_cancellation: forall m n l, m ∈ ω -> n ∈ ω -> l ∈ ω ->*)
  (*m +ₙ l = n +ₙ l -> m = n.*)
(*Proof.*)
  (*intros m n l P1 P2 P3 P4.*)
  (*pose (P := fun k => m +ₙ k = n +ₙ k -> m = n).*)
  (*assert (P n.0) as I1.*)
  (*{ intros Q1.*)
    (*rewrite (add_zero _ P1) in Q1.*)
    (*rewrite (add_zero _ P2) in Q1.*)
    (*apply Q1. }*)
  (*assert (induction_step P) as I2.*)
  (*{ intros k Q1 Q2 Q3.*)
    (*rewrite (add_red _ _ P1 Q1) in Q3.*)
    (*rewrite (add_red _ _ P2 Q1) in Q3.*)
    (*apply (Q2 (suc_unique _ _ *)
      (*(add_is_nat _ _ P1 Q1) (add_is_nat _ _ P2 Q1) Q3)). }*)
  (*apply (induction_principle _ I1 I2 _ P3 P4).*)
(*Qed.*)

(*Lemma add_cancellation_2: forall m n p q, p = q -> m +ₙ p = n +ₙ q -> *)
  (*m ∈ ω -> n ∈ ω -> p ∈ ω -> q ∈ ω -> m = n.*)
(*Proof.*)
  (*intros m n p q P1 P2 P3 P4 P5 P6.*)
  (*rewrite P1 in P2.*)
  (*apply (add_cancellation _ _ _ P3 P4 P6 P2).*)
(*Qed.*)

(*Lemma add_cancellation_inverse: forall m n l, m = n -> m +ₙ l = n +ₙ l.*)
(*Proof.*)
  (*intros m n l P1.*)
  (*rewrite P1.*)
  (*reflexivity.*)
(*Qed.*)

(*Lemma mul_equation: forall a b c d, a = b -> c = d -> a ×ₙ c = b ×ₙ d.*)
(*Proof.*)
  (*intros a b c d P1 P2.*)
  (*rewrite P1.*)
  (*rewrite P2.*)
  (*reflexivity.*)
(*Qed.*)

(*Lemma mul_equation_2: forall a b c, a = b -> a ×ₙ c = b ×ₙ c.*)
(*Proof.*)
  (*intros a b c P1.*)
  (*rewrite P1.*)
  (*reflexivity.*)
(*Qed.*)

(*Lemma add_cyc: forall m n l, m ∈ ω -> n ∈ ω -> l ∈ ω -> *)
  (*(m +ₙ n) +ₙ l = (m +ₙ l) +ₙ n.*)
(*Proof.*)
  (*intros m n l P1 P2 P3.*)
  (*rewrite <- (add_associative _ _ _ P1 P3 P2).*)
  (*rewrite (add_commutative _ _ P3 P2).*)
  (*rewrite (add_associative _ _ _ P1 P2 P3).*)
  (*reflexivity.*)
(*Qed.*)

(*Lemma mul_cyc: forall m n l, m ∈ ω -> n ∈ ω -> l ∈ ω -> *)
  (*(m ×ₙ n) ×ₙ l = (m ×ₙ l) ×ₙ n.*)
(*Proof.*)
  (*intros m n l P1 P2 P3.*)
  (*rewrite <- (mul_associative _ _ _ P1 P3 P2).*)
  (*rewrite (mul_commutative _ _ P3 P2).*)
  (*rewrite (mul_associative _ _ _ P1 P2 P3).*)
  (*reflexivity.*)
(*Qed.*)

(*Lemma mul_cyc_2: forall m n l, m ∈ ω -> n ∈ ω -> l ∈ ω -> *)
  (*(m ×ₙ n) ×ₙ l = (l ×ₙ m) ×ₙ n.*)
(*Proof.*)
  (*intros m n l P1 P2 P3.*)
  (*rewrite <- (mul_associative _ _ _ P3 P1 P2).*)
  (*rewrite (mul_commutative _ _ P3 (mul_is_nat _ _ P1 P2)).*)
  (*reflexivity.*)
(*Qed.*)
(*[>----------------------------------------------------------------------------<]*)

(*[> Ltac <]*)
(*[> Flow: add enough equation into the goal <]*)
(*[>       run nat_normal_form to normalize it <]*)
(*[>       exchange order of mulple (I don't know how to do it automaticly now) <]*)
(*[>       run nat_rea to reduce result <]*)
(*[>       run is_nat to clean up <]*)
(*Ltac is_nat :=*)
  (*repeat match goal with*)
    (*| [       |- ?P = ?P         ] => reflexivity*)
    (*| [       |- n.0 ∈ ω         ] => apply empty_is_nat*)
    (*| [       |- n.1 ∈ ω         ] => apply one_is_nat*)
    (*| [ H: ?P |- ?P              ] => apply H*)
    (*| [       |- ⟨_, _⟩ ∈ cp _ _ ] => apply cp_intro*)
    (*| [       |- (S(_)) ∈ ω      ] => apply suc_is_nat*)
    (*| [       |- ?P +ₙ ?Q ∈ ω    ] => apply add_is_nat*)
    (*| [       |- ?P ×ₙ ?Q ∈ ω    ] => apply mul_is_nat*)
  (*end.*)

(*Ltac nat_unwrap_mul_ M :=*)
  (*repeat match M with*)
    (*| ?R ×ₙ (?P +ₙ ?Q) => rewrite (distributive_l R P Q)*)
    (*| (?P +ₙ ?Q) ×ₙ ?R => rewrite (mul_commutative (P +ₙ Q) R)*)
    (*| ?P ×ₙ (?Q ×ₙ ?R) => rewrite (mul_commutative P (Q ×ₙ R))*)
    (*| ?P ×ₙ ?Q         => nat_unwrap_mul_ P; nat_unwrap_mul_ Q*)
    (*| ?P +ₙ ?Q         => nat_unwrap_mul_ P; nat_unwrap_mul_ Q*)
  (*end.*)

(*Ltac nat_unwrap_mul :=*)
  (*repeat match goal with*)
    (*| [ |- ?P = ?Q ] => nat_unwrap_mul_ P; nat_unwrap_mul_ Q*)
  (*end.*)

(*Ltac nat_unwrap_add_ M :=*)
  (*repeat match M with*)
    (*| ?P +ₙ (?Q +ₙ ?R) => rewrite (add_associative P Q R)*)
    (*| ?P +ₙ ?Q         => nat_unwrap_add_ P*)
  (*end.*)

(*Ltac nat_unwrap_add :=*)
  (*repeat match goal with*)
    (*| [ |- ?P = ?Q ] => nat_unwrap_add_ P; nat_unwrap_add_ Q*)
  (*end.*)

(*Ltac nat_normal_form :=*)
  (*nat_unwrap_mul;*)
  (*nat_unwrap_add.*)

(*Ltac nat_red_ M P :=*)
  (*repeat match M with*)
    (*[>| P              => assumption<]*)
    (*[>| _ +ₙ P         => assumption [>do nothing<]<]*)
    (*| P +ₙ ?Q        => rewrite (add_commutative P Q)*)
    (*| (?R +ₙ P) +ₙ ?Q => rewrite (add_cyc R P Q)*)
    (*| ?Q +ₙ _        => nat_red_ Q P*)
  (*end.*)

(*Ltac nat_red :=*)
  (*repeat match goal with*)
    (*| [ |- ?P               = ?P      ] => reflexivity*)
    (*| [ |- _          +ₙ ?P = _ +ₙ ?P ] => apply add_cancellation_inverse*)
    (*| [ |- ?P         +ₙ ?Q = _ +ₙ ?P ] => rewrite (add_commutative P Q)*)
    (*| [ |- (?R +ₙ ?P) +ₙ ?Q = _ +ₙ ?P ] => rewrite (add_cyc R P Q)*)
    (*| [ |- ?R         +ₙ _  = _ +ₙ ?P ] => repeat nat_red_ R P*)
  (*end.*)


(*Lemma test: forall a b c d, a ∈ ω -> b ∈ ω -> c ∈ ω -> d ∈ ω ->*)
  (*(a ×ₙ b) +ₙ a ×ₙ (c +ₙ d) ×ₙ (a +ₙ b) = a ×ₙ (c +ₙ d) ×ₙ (a +ₙ b) +ₙ (a ×ₙ b).*)
(*Proof.*)
  (*intros a b c d P1 P2 P3 P4.*)
  (*nat_normal_form.*)
  (*nat_red.*)
  (*all: is_nat.*)
(*Qed.*)
(*[>----------------------------------------------------------------------------<]*)
