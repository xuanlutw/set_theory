Require Import Init.Init.
Require Import Relation.Relation.
Require Import Nat.Inductive.
Require Import Nat.Nature.
Require Import Nat.Recursion.

(*Require dpdgraph.dpdgraph.*)

Definition nat0 := (∅).
Definition nat1 := (S(nat0)).
Definition nat2 := (S(nat1)).
Notation "𝟢"    := (nat0).
Notation "𝟣"    := (nat1).
Notation "𝟤"    := (nat2).

Definition sigma := {x: ω ⨉ ω| ∃ y, x = ⟨y, S(y)⟩}.
Notation   "'σ'" := (sigma).

Definition add_proto (m: J) := (ex_outl (recursion_thm ω m σ)).
Definition mul_proto (m: J) := (ex_outl (recursion_thm ω (𝟢) (add_proto m))).
Definition exp_proto (m: J) := (ex_outl (recursion_thm ω (𝟣) (mul_proto m))).

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
 
Lemma zero_is_nat: 𝟢 ∈ ω.
Proof.
  apply empty_is_nat.
Qed.

Lemma one_is_nat: 𝟣 ∈ ω.
Proof.
  apply (suc_is_nat _ zero_is_nat).
Qed.

Lemma add_zero: ∀ m, m ∈ ω → m +ₙ 𝟢 = m.
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

Theorem one_one_two: 𝟣 +ₙ 𝟣 = 𝟤.
Proof.
  apply (eq_cr (λ x, x = 𝟤) (add_red (𝟣) (𝟢) one_is_nat zero_is_nat)).
  apply (eq_cr (λ x, S(x) = 𝟤) (add_zero (𝟣) one_is_nat)).
  apply eq_r.
Qed.
(*----------------------------------------------------------------------------*)

(* Multiplication *)
Lemma mul_proto_is_fn: ∀ m, m ∈ ω → fnm (mul_proto m) ω ω.
Proof.
  intros m P1.
  destruct (ex_outr (recursion_thm ω (𝟢) (add_proto m)) 
    (zero_is_nat) (add_proto_is_fn _ P1)) as [P2 _].
  apply P2.
Qed.

Lemma mul_proto_e1: ∀ m, m ∈ ω → (mul_proto m)[𝟢] = 𝟢.
Proof.
  intros m P1.
  destruct (ex_outr (recursion_thm ω (𝟢) (add_proto m)) 
    (zero_is_nat) (add_proto_is_fn _ P1)) as [_ [P2 _]].
  apply P2.
Qed.

Lemma mul_proto_e2: ∀ m, ∀ n, m ∈ ω → n ∈ ω → 
    (mul_proto m)[S(n)] = (add_proto m)[(mul_proto m)[n]].
Proof.
  intros m n P1 P2.
  destruct (ex_outr (recursion_thm ω (𝟢) (add_proto m)) 
    (zero_is_nat) (add_proto_is_fn _ P1)) as [_ [_ P3]].
  apply (P3 _ P2).
Qed. 

Lemma mul_zero: ∀ m, m ∈ ω → m ×ₙ 𝟢 = 𝟢.
Proof.
  intros m P1.
  apply (mul_proto_e1 _ P1).
Qed.

Lemma mul_red: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m ×ₙ S(n) = m +ₙ (m ×ₙ n).
Proof.
  intros m n P1 P2.
  apply (mul_proto_e2 _ _ P1 P2).
Qed.

Lemma mul_one: ∀ m, m ∈ ω → m ×ₙ 𝟣 = m.
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
  destruct (ex_outr (recursion_thm ω (𝟣) (mul_proto m)) 
    one_is_nat (mul_proto_is_fn _ P1)) as [P2 _].
  apply P2.
Qed.

Lemma exp_proto_e1: ∀ m, m ∈ ω → (exp_proto m)[𝟢] = 𝟣.
Proof.
  intros m P1.
  destruct (ex_outr (recursion_thm ω (𝟣) (mul_proto m)) 
    one_is_nat (mul_proto_is_fn _ P1)) as [_ [P2 _]].
  apply P2.
Qed.

Lemma exp_proto_e2: ∀ m, ∀ n, m ∈ ω → n ∈ ω → 
    (exp_proto m)[S(n)] = (mul_proto m)[(exp_proto m)[n]].
Proof.
  intros m n P1 P2.
  destruct (ex_outr (recursion_thm ω (𝟣) (mul_proto m)) 
    one_is_nat (mul_proto_is_fn _ P1)) as [_ [_ P3]].
  apply (P3 _ P2).
Qed.

Lemma exp_zero: ∀ m, m ∈ ω → m ^ₙ 𝟢 = 𝟣.
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

Ltac is_nat :=
  repeat match goal with
    | [       |- ?P = ?P         ] => apply eq_r
    | [       |- 𝟢 ∈ ω           ] => apply empty_is_nat
    | [       |- 𝟣 ∈ ω           ] => apply one_is_nat
    | [ H: ?P |- ?P              ] => apply H
    | [       |- ⟨_, _⟩ ∈ cp _ _ ] => apply cp_i
    | [       |- (S(_)) ∈ ω      ] => apply suc_is_nat
    | [       |- ?P +ₙ ?Q ∈ ω    ] => apply add_is_nat
    | [       |- ?P ×ₙ ?Q ∈ ω    ] => apply mul_is_nat
  end.

(* Arith Law *)
Lemma add_zero_l: ∀ m, m ∈ ω → 𝟢 +ₙ m = m.
Proof.
  intros m P1.
  pose (λ k, 𝟢 +ₙ k = k) as P.
  assert (P 𝟢) as I1.
  { apply (add_zero _ empty_is_nat). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2.
    apply (eq_cr (λ x, x = _) (add_red _ _ empty_is_nat Q1)).
    apply (eq_cr (λ x, S(x) = _) Q2).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P1).
Qed.

Lemma add_red_l: ∀ m, ∀ n, m ∈ ω → n ∈ ω → S(m) +ₙ n = S(m +ₙ n).
Proof.
  intros m n P1 P2.
  pose (λ k, S(m) +ₙ k = S(m +ₙ k)) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, x = _) (add_zero _ (suc_is_nat _ P1))).
    apply (eq_cr (λ x, _ = S(x)) (add_zero _ P1)).
    apply eq_r. }
  assert (induction_step P) as I2.
  { intros k Q1 Q2.
    apply (eq_cr (λ x, x = _) (add_red _ _ (suc_is_nat _ P1) Q1)).
    apply (eq_cr (λ x, S(x) = _) Q2).
    apply (eq_cr (λ x, _ = S(x)) (add_red _ _ P1 Q1)).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P2).
Qed.

Lemma add_commu: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m +ₙ n = n +ₙ m.
Proof.
  intros m n P1 P2.
  pose (λ k, m +ₙ k = k +ₙ m) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, x = _) (add_zero _ P1)).
    apply (eq_cr (λ x, _ = x) (add_zero_l _ P1)).
    apply eq_r. }
  assert (induction_step P) as I2.
  { intros k P4 P5.
    apply (eq_cr (λ x, x = _) (add_red _ _ P1 P4)).
    apply (eq_cr (λ x, _ = x) (add_red_l _ _ P4 P1)).
    apply (eq_cl (λ x, _ = S(x)) P5).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P2).
Qed.

Lemma add_assoc: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω
  → m +ₙ (n +ₙ p) = (m +ₙ n) +ₙ p.
Proof.
  intros m n p P1 P2 P3.
  pose (λ k, m +ₙ (n +ₙ k) = (m +ₙ n) +ₙ k) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, _ +ₙ x = _) (add_zero _ P2)).
    apply eq_s.
    apply add_zero.
    is_nat. }
  assert (induction_step P) as I2.
  { intros k P5 P6.
    red.
    apply (eq_cr (λ x, _ = x) (add_red (m +ₙ n) k (add_is_nat _ _ P1 P2) P5)).
    apply (eq_cl (λ x, _ = S(x)) P6).
    apply (eq_cr (λ x, _ +ₙ x = _) (add_red _ _ P2 P5)).
    apply (eq_cr (λ x, x = _) (add_red _ _ P1 (add_is_nat _ _ P2 P5))).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P3).
Qed.

Lemma mul_zero_l: ∀ m, m ∈ ω → 𝟢 ×ₙ m = 𝟢.
Proof.
  intros m P1.
  pose (λ k, 𝟢 ×ₙ k = 𝟢) as P.
  assert (P 𝟢) as I1.
  { apply (mul_zero _ empty_is_nat). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2.
    apply (eq_cr (λ x, x = _) (mul_red _ _ empty_is_nat Q1)).
    apply (eq_cr (λ x, _ +ₙ x = _) Q2).
    apply (add_zero _ empty_is_nat). }
  apply (induction_principle _ I1 I2 _ P1).
Qed.

Lemma mul_red_l: ∀ m, ∀ n, m ∈ ω → n ∈ ω → S(m) ×ₙ n = n +ₙ (m ×ₙ n).
Proof.
  intros m n P1 P2.
  pose (λ k, S(m) ×ₙ k = k +ₙ (m ×ₙ k)) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, x = _) (mul_zero _ (suc_is_nat _ P1))).
    apply (eq_cr (λ x, _ = _ +ₙ x) (mul_zero _ P1)).
    apply (eq_cr (λ x, _ = x) (add_zero _ empty_is_nat)).
    apply eq_r. }
  assert (induction_step P) as I2.
  { intros k P4 P5.
    apply (eq_cr (λ x, x = _) (mul_red _ _ (suc_is_nat _ P1) P4)).
    apply (eq_cr (λ x, _ = _ +ₙ x) (mul_red _ _ P1 P4)).
    apply (eq_cr (λ x, _ +ₙ x = _) P5).
    apply (eq_cr (λ x, x = _)
      (add_assoc _ _ _ (suc_is_nat _ P1) P4 (mul_is_nat _ _ P1 P4))).
    apply (eq_cr (λ x, _ = x)
      (add_assoc _ _ _ (suc_is_nat _ P4) P1 (mul_is_nat _ _ P1 P4))).
    apply (eq_cr (λ x, _ = x +ₙ _) (add_commu _ _ (suc_is_nat _ P4) P1)).
    apply (eq_cr (λ x, _ = x +ₙ _) (add_red _ _ P1 P4)).
    apply (eq_cr (λ x, x +ₙ _ = _) (add_red_l _ _ P1 P4)).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P2).
Qed.

Lemma distr_l: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω
  → m ×ₙ (n +ₙ p) = m ×ₙ n +ₙ m ×ₙ p.
Proof.
  intros m n p P1 P2 P3.
  pose (λ k, m ×ₙ (n +ₙ k) = m ×ₙ n +ₙ m ×ₙ k) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, _ ×ₙ x = _) (add_zero _ P2)).
    apply (eq_cr (λ x, _ = _ +ₙ x) (mul_zero _ P1)).
    apply (eq_cr (λ x, _ = x) (add_zero _ (mul_is_nat _ _ P1 P2))).
    apply eq_r. }
  assert (induction_step P) as I2.
  { intros k P5 P6.
    apply (eq_cr (λ x, _ ×ₙ x = _) (add_red _ _ P2 P5)).
    apply (eq_cr (λ x, x = _) (mul_red _ _ P1 (add_is_nat _ _ P2 P5))).
    apply (eq_cr (λ x, _ +ₙ x = _) P6).
    apply (eq_cr (λ x, _ = _ +ₙ x) (mul_red _ _ P1 P5)).
    apply (eq_cr (λ x, _ = x)
      (add_assoc _ _ _ (mul_is_nat _ _ P1 P2) P1 (mul_is_nat _ _ P1 P5))).
    apply (eq_cr (λ x, _ = x +ₙ _) (add_commu _ _ (mul_is_nat _ _ P1 P2) P1)).
    apply (eq_cr (λ x, x = _)
      (add_assoc _ _ _ P1 (mul_is_nat _ _ P1 P2) (mul_is_nat _ _ P1 P5))).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P3).
Qed.

Lemma mul_commu: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m ×ₙ n = n ×ₙ m.
Proof.
  intros m n P1 P2.
  pose (λ k, m ×ₙ k = k ×ₙ m) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, x = _) (mul_zero _ P1)).
    apply (eq_cr (λ x, _ = x) (mul_zero_l _ P1)).
    apply eq_r. }
  assert (induction_step P) as I2.
  { intros k P4 P5.
    apply (eq_cr (λ x, x = _) (mul_red _ _ P1 P4)).
    apply (eq_cr (λ x, _ = x) (mul_red_l _ _ P4 P1)).
    apply (eq_cr (λ x, _ +ₙ x = _) P5).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P2).
Qed.

Lemma mul_assoc: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω
  → m ×ₙ (n ×ₙ p) = (m ×ₙ n) ×ₙ p.
Proof.
  intros m n p P1 P2 P3.
  pose (λ k, m ×ₙ (n ×ₙ k) = (m ×ₙ n) ×ₙ k) as P.
  assert (P 𝟢) as I1.
  { apply (eq_cr (λ x, _ ×ₙ x = _) (mul_zero _ P2)).
    apply (eq_cr (λ x, x = _) (mul_zero _ P1)).
    apply (eq_cr (λ x, _ = x) (mul_zero _ (mul_is_nat _ _ P1 P2))).
    apply eq_r. }
  assert (induction_step P) as I2.
  { intros k P5 P6.
    apply (eq_cr (λ x, _ = x) (mul_red _ _ (mul_is_nat _ _ P1 P2) P5)).
    apply (eq_cl (λ x, _ = _ +ₙ x) P6).
    apply (eq_cr (λ x, _ ×ₙ x = _) (mul_red _ _ P2 P5)).
    apply (eq_cr (λ x, x = _) (distr_l _ _ _ P1 P2 (mul_is_nat _ _ P2 P5))).
    apply eq_r. }
  apply (induction_principle _ I1 I2 _ P3).
Qed.

Lemma mul_eq_zero: ∀ m, ∀ n, m ∈ ω → n ∈ ω → m ×ₙ n = 𝟢 → m = 𝟢 ∨ n = 𝟢.
Proof.
  intros m n P1 P2.
  apply contraposition4.
  intros P3 P4.
  destruct (not_or_and P3) as [P5 P6].
  destruct (nat_is_suc _ P1 P5) as [mm [P7 P8]].
  destruct (nat_is_suc _ P2 P6) as [nn [P9 P10]].
  apply (empty_not_suc (nn +ₙ mm ×ₙ S( nn))).
  apply (eq_cl (λ x, _ = x)
    (add_red_l _ _ P9 (mul_is_nat _ _ P7 (suc_is_nat _ P9)))).
  apply (eq_cl (λ x, _ = x +ₙ _ ×ₙ x) P10).
  apply (eq_cl (λ x, _ = x) (mul_red_l _ _ P7 P2)).
  apply (eq_cl (λ x, _ = x ×ₙ _) P8).
  apply (eq_s P4).
Qed.

Lemma distr_r: ∀ m, ∀ n, ∀ p, m ∈ ω → n ∈ ω → p ∈ ω
  → (m +ₙ n) ×ₙ p = m ×ₙ p +ₙ n ×ₙ p.
Proof.
  intros m n p P1 P2 P3.
  apply (eq_cr (λ x, x = _) (mul_commu _ _ (add_is_nat _ _ P1 P2) P3)).
  apply (eq_cr (λ x, _ = x +ₙ _) (mul_commu _ _ P1 P3)).
  apply (eq_cr (λ x, _ = _ +ₙ x) (mul_commu _ _ P2 P3)).
  apply (distr_l _ _ _ P3 P1 P2).
Qed.

Lemma add_eq: ∀ a, ∀ b, ∀ c, ∀ d, a = b → c = d → a +ₙ c = b +ₙ d.
Proof.
  intros a b c d P1 P2.
  apply (eq_cr (λ x, x +ₙ _ = _) P1).
  apply (eq_cr (λ x, _ +ₙ x = _) P2).
  apply eq_r.
Qed.

Lemma add_eq_2: ∀ m, ∀ n, ∀ l, m = n → m +ₙ l = n +ₙ l.
Proof.
  intros m n l P1.
  apply (add_eq _ _ _ _ P1 (eq_r _)).
Qed.

Lemma add_cancel: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m +ₙ l = n +ₙ l → m = n.
Proof.
  intros m n l P1 P2 P3 P4.
  pose (λ k, m +ₙ k = n +ₙ k → m = n) as P.
  assert (P 𝟢) as I1.
  { intros Q1.
    apply (eq_t (eq_s (add_zero _ P1)) (eq_t Q1 (add_zero _ P2))). }
  assert (induction_step P) as I2.
  { intros k Q1 Q2 Q3.
    pose (add_red _ _ P1 Q1) as Q4.
    pose (add_red _ _ P2 Q1) as Q5.
    pose (eq_t (eq_s Q4) (eq_t Q3 Q5)) as Q6.
    apply Q2.
    apply suc_unique.
    all: is_nat. }
  apply (induction_principle _ I1 I2 _ P3 P4).
Qed.

Lemma add_cancel_2: ∀ m, ∀ n, ∀ p, ∀ q, p = q → m +ₙ p = n +ₙ q
  → m ∈ ω → n ∈ ω → p ∈ ω → q ∈ ω → m = n.
Proof.
  intros m n p q P1 P2 P3 P4 P5 P6.
  pose (eq_cl (λ x, _ +ₙ x = _) P1 P2) as P7.
  apply (add_cancel _ _ _ P3 P4 P6 P7).
Qed.

Lemma mul_eq: ∀ a, ∀ b, ∀ c, ∀ d, a = b → c = d → a ×ₙ c = b ×ₙ d.
Proof.
  intros a b c d P1 P2.
  apply (eq_cr (λ x, x ×ₙ _ = _) P1).
  apply (eq_cr (λ x, _ ×ₙ x = _) P2).
  apply eq_r.
Qed.

Lemma mul_eq_2: ∀ a, ∀ b, ∀ c, a = b → a ×ₙ c = b ×ₙ c.
Proof.
  intros a b c P1.
  apply (mul_eq _ _ _ _ P1 (eq_r _)).
Qed.

Lemma add_132: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m +ₙ n +ₙ l = m +ₙ l +ₙ n.
Proof.
  intros m n l P1 P2 P3.
  apply (eq_cl (λ x, _ = x) (add_assoc _ _ _ P1 P3 P2)).
  apply (eq_cr (λ x, _ = _ +ₙ x) (add_commu _ _ P3 P2)).
  apply (eq_cr (λ x, _ = x) (add_assoc _ _ _ P1 P2 P3)).
  apply eq_r.
Qed.

Lemma add_213: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m +ₙ n +ₙ l = n +ₙ m +ₙ l.
Proof.
  intros m n l P1 P2 P3.
  apply (eq_cr (λ x, _ = x +ₙ _) (add_commu _ _ P2 P1)).
  apply eq_r.
Qed.

Lemma add_231: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m +ₙ n +ₙ l = n +ₙ l +ₙ m.
Proof.
  intros m n l P1 P2 P3.
  apply (eq_cl (λ x, _ = x) (add_assoc _ _ _ P2 P3 P1)).
  apply (eq_cr (λ x, _ = _ +ₙ x) (add_commu _ _ P3 P1)).
  apply (eq_cr (λ x, _ = x) (add_assoc _ _ _ P2 P1 P3)).
  apply (add_213 _ _ _ P1 P2 P3).
Qed.

Lemma add_312: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m +ₙ n +ₙ l = l +ₙ m +ₙ n.
Proof.
  intros m n l P1 P2 P3.
  apply (eq_cr (λ x, _ = x +ₙ _) (add_commu _ _ P3 P1)).
  apply (add_132 _ _ _ P1 P2 P3).
Qed.

Lemma add_321: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m +ₙ n +ₙ l = l +ₙ n +ₙ m.
Proof.
  intros m n l P1 P2 P3.
  apply (eq_cr (λ x, _ = x +ₙ _) (add_commu _ _ P3 P2)).
  apply (add_231 _ _ _ P1 P2 P3).
Qed.

Lemma mul_132: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m ×ₙ n ×ₙ l = m ×ₙ l ×ₙ n.
Proof.
  intros m n l P1 P2 P3.
  apply (eq_cl (λ x, _ = x) (mul_assoc _ _ _ P1 P3 P2)).
  apply (eq_cr (λ x, _ = _ ×ₙ x) (mul_commu _ _ P3 P2)).
  apply (eq_cr (λ x, _ = x) (mul_assoc _ _ _ P1 P2 P3)).
  apply eq_r.
Qed.

Lemma mul_213: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m ×ₙ n ×ₙ l = n ×ₙ m ×ₙ l.
Proof.
  intros m n l P1 P2 P3.
  apply (eq_cr (λ x, _ = x ×ₙ _) (mul_commu _ _ P2 P1)).
  apply eq_r.
Qed.

Lemma mul_231: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m ×ₙ n ×ₙ l = n ×ₙ l ×ₙ m.
Proof.
  intros m n l P1 P2 P3.
  apply (eq_cl (λ x, _ = x) (mul_assoc _ _ _ P2 P3 P1)).
  apply (eq_cr (λ x, _ = _ ×ₙ x) (mul_commu _ _ P3 P1)).
  apply (eq_cr (λ x, _ = x) (mul_assoc _ _ _ P2 P1 P3)).
  apply (mul_213 _ _ _ P1 P2 P3).
Qed.

Lemma mul_312: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m ×ₙ n ×ₙ l = l ×ₙ m ×ₙ n.
Proof.
  intros m n l P1 P2 P3.
  apply (eq_cr (λ x, _ = x ×ₙ _) (mul_commu _ _ P3 P1)).
  apply (mul_132 _ _ _ P1 P2 P3).
Qed.

Lemma mul_321: ∀ m, ∀ n, ∀ l, m ∈ ω → n ∈ ω → l ∈ ω
  → m ×ₙ n ×ₙ l = l ×ₙ n ×ₙ m.
Proof.
  intros m n l P1 P2 P3.
  apply (eq_cr (λ x, _ = x ×ₙ _) (mul_commu _ _ P3 P2)).
  apply (mul_231 _ _ _ P1 P2 P3).
Qed.
(*[>----------------------------------------------------------------------------<]*)

(*Ltac *)
(*Flow: add enough equation into the goal *)
      (*run nat_normal_form to normalize it *)
      (*exchange order of mulple (I don't know how to do it automaticly now) *)
      (*run nat_rea to reduce result *)
      (*run is_nat to clean up *)
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
