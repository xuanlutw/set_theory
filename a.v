Parameter set      : Prop.
Parameter set_in   : set -> set -> Prop.
Definition set_in2 x y := (set_in y x).
Infix     "∈"     := set_in2                      (at level 70).
Notation  "x ∉  y" := (~ (set_in2 x y))            (at level 70).
Notation  "x ⊆ y" := (forall a, a ∈ x -> a ∈ y) (at level 72).

(* Logic *)
Axiom LEM: forall P: Prop, P \/ ~P.

Lemma NN_elim: forall P: Prop, ~~P -> P.
Proof.
  intros P H1.
  pose (H2 := LEM P).
  destruct H2.
  assumption.
  contradiction.
Qed.

Lemma NN_intro: forall P: Prop, P -> ~~P.
Proof.
  intros P H1 H2.
  contradiction.
Qed.

Lemma contraposition: forall P Q: Prop, (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  intro.
  apply H0.
  apply H.
  assumption.
Qed.

Lemma contraposition2: forall P Q: Prop, (~P -> Q) -> (~Q -> P).
Proof.
  intros P Q H1 H2.
  pose (H3 := contraposition (~P) Q H1).
  apply H3 in H2.
  apply NN_elim.
  assumption.
(*  apply contraposition.*)
(*  assert ((~P -> Q) -> ~Q -> ~~P) as H1.*)
(*  apply contraposition.*)
(*  assert (~~P -> P) as H2.*)
(*  apply NN_elim.*)
(*  intros Q1 Q2.*)
(*  apply H2.*)
(*  apply H1.*)
(*  assumption.*)
(*  assumption.*)
Qed.

Lemma contraposition3: forall P Q: Prop, (P -> ~Q) -> (Q -> ~P).
Proof.
  intros P Q H1 H2.
  pose (H3 := contraposition P (~Q) H1).
  apply H3.
  apply NN_intro.
  assumption.
Qed.

Lemma contraposition4: forall P Q: Prop, (~P -> ~Q) -> (Q -> P).
Proof.
  intros P Q H1 H2.
  pose (H3 := contraposition3 (~P) Q H1).
  apply NN_elim.
  apply H3.
  apply H2.
Qed.

Lemma not_and_or: forall P Q: Prop, ~(P /\ Q) -> ~P \/ ~Q.
Proof.
  intros P Q H1.
  pose (HP := LEM P).
  destruct HP.
  pose (HQ := LEM Q).
  destruct HQ.
  
  assert (P /\ Q).
  split. assumption. assumption.
  contradiction.

  right.
  assumption.

  left.
  assumption.
Qed.

Lemma not_or_and: forall P Q: Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q H1.
  split.

  pose (HP := LEM P).
  destruct HP.
  assert (P \/ Q) as G.
  left. assumption.
  contradiction.
  assumption.

  pose (HQ := LEM Q).
  destruct HQ.
  assert (P \/ Q) as G.
  right. assumption.
  contradiction.
  assumption.
Qed.

Lemma and_not_or: forall P Q: Prop, ~P /\ ~Q -> ~(P \/ Q).
Proof.
  intros P Q H1 H2.
  destruct H1.
  destruct H2.
  contradiction.
  contradiction.
Qed.

Lemma or_not_and: forall P Q: Prop, ~P \/ ~Q -> ~(P /\ Q).
Proof.
  intros P Q H1 H2.
  destruct H2.
  destruct H1.
  contradiction.
  contradiction.
Qed.

Lemma not_exists_forall_not: forall P: set -> Prop, ~(exists A: set, P A) -> (forall A: set, ~(P A)).
Proof.
  intros P H1 A H2.
  assert (exists A, P A).
  exists A.
  assumption.
  contradiction.
Qed.

(* Skip*)
Definition eqs x y := (forall a, ((a ∈ x) -> (a ∈ y)) /\ ((a ∈ y) -> (a∈ x))).
Notation "x =ₛ y" := (@eqs x y) (at level 10).  

Lemma set_eq_t: forall x y z, (x =ₛ y) /\ (y =ₛ z) -> (x =ₛ z).
Proof.
  unfold eqs.
  intros.
  destruct H.
  destruct (H a) as [p0].
  destruct (H0 a) as [p1].
  split.
    intros.
    apply p0 in H3.
    apply p1 in H3.
    assumption. 
    intros.
    apply H2 in H3.
    apply H1 in H3.
    assumption. 
Qed.
Check set_eq_t .

Axiom exten: forall A B, (forall x, x ∈ A <-> x ∈ B) -> A = B.
Parameter emptyset  : set.
Notation "∅" := emptyset.
Axiom empty: forall x, x ∉  ∅.

Lemma subset_eq: forall (A: set) (B: set), A ⊆ B /\ B ⊆ A -> A = B.
Proof.
  intros.
  destruct H.
  assert ((forall x, x ∈ A <-> x ∈ B) -> A = B).
  apply (exten).
  elim H1.
  trivial.
  intro.
  split.
  specialize (H x).
  assumption.
  specialize (H0 x).
  assumption.
Qed.

Lemma sub_self: forall A, A ⊆ A.
Proof.
  intros.
  apply H.
Qed.

Lemma in_subset_in: forall x A B, x ∈ A -> A ⊆ B -> x ∈ B.
Proof.
  intros.
  pose (H1 := H0 x).
  apply H1.
  apply H.
Qed.

Lemma empty_all_subset: forall (A: set), (forall (a: set), a ∉ A) -> (forall (B: set), A ⊆B).
Proof.
  intros.
  specialize (H a).
  absurd (a ∈ A).
  assumption.
  assumption.
Qed.

Lemma empty_all_subset2: (forall (B: set), ∅ ⊆B).
Proof.
  apply (empty_all_subset).
  apply (empty).
Qed.

Lemma empty_unique: forall (A: set), (forall (B: set), B ∉ A) -> A = ∅ .
Proof.
  intro.
  intro.
  assert (A ⊆ ∅).
  apply (empty_all_subset).
  assumption.
  assert (∅ ⊆ A).
  apply (empty_all_subset2).
  apply (subset_eq).
  split. 
  assumption.
  assumption.
Qed.

Lemma at_least: forall (A: set), A <> ∅  -> (exists (a: set), a ∈ A).
Proof.
  intro S.
  apply (contraposition2).
  intro H1.
  apply (empty_unique).
  pose (H2 := not_exists_forall_not (set_in S) H1).
  apply H2.
(*  apply *)
(*  assert ((~(exists (a: set), a ∈ A) -> A = ∅ )).*)
(*  intro.*)
(*  assert (forall a, a ∉ A).*)
(*  apply (not_exists_forall_not). assumption.*)
(*  apply (empty_unique). assumption.*)
(*  apply e.*)
(*  apply H.*)
(**)
(*  assert ((~(exists (a: set), a ∈ A) -> A = ∅ ) -> (A <> ∅ -> (exists a, a ∈ A))).*)
(*  apply (contraposition2).*)
(*  assert ((~(exists (a: set), a ∈ A) -> A = ∅ )).*)
(*  intro.*)
(*  assert (forall a, a ∉ A).*)
(*  apply (not_exists_forall_not). assumption.*)
(*  apply (empty_unique). assumption.*)
(*  apply e.*)
(*  apply H. *)
Qed.

Definition proj1_exists :=
fun {A : Prop} {P : A -> Prop} (e : exists x : A , P x) =>
let (a, _) := e in a.

Definition proj2_exists :=
fun {A : Prop} {P : A -> Prop} (e : exists x : A , P x) =>
let (a, b) as e0 return (P (proj1_exists e0)) := e in b.

Axiom pair: forall A B: set, exists C: set, forall x, x ∈ C <-> (x ∈ A /\ x ∈ B).

Definition pair_builder (A: set) (B: set) := proj1_exists(pair A B).

Notation "{ A B }" := (pair_builder A B)(at level 72).

Definition singleton (A: set) := pair_builder A A.

Notation "{ A }ₛ" := (singleton A)(at level 100).

Axiom power: forall a, exists B, forall x, (x ∈ B <-> x ⊆ a). 

Axiom separ: forall (A: set) (P: set -> Prop), exists (B:set),
  forall (x: set), x ∈ B <-> x ∈ A /\ P x.

Ltac intro_subset A P :=
  pose (G := separ A P); destruct G.

Definition set_builder ( x : set ) ( P : set -> Prop ) :=
  proj1_exists ( separ x P ).

Notation "{ x ∈ y | P }" :=
  (set_builder y (fun x=>P)) (at level 0, x at level 49).

Definition power_builder (x: set) := proj1_exists (power x).

Notation "P( x )" := (power_builder x) (at level 88).

Lemma power_in: forall A, A ∈ (P(A)).
Proof.
  intros.
  pose (H0 := proj2_exists(power A)).
  pose (H1 := H0 A).
  destruct H1.
  apply H1.
  apply sub_self.
Qed.

Lemma power_sub: forall A x, x ∈ (P(A)) -> x ⊆ A.
Proof.
  intros A x H1.
  pose (H2 := proj2_exists(power A)).
  pose (H3 := H2 x).
  destruct H3.
  apply H.
  apply H1.
Qed.

Lemma two: forall (A B: Prop), ~((A -> B /\ ~A) /\ (B /\ ~A -> A) /\ B).
Proof.
  red.
  intros.
  destruct H.
  destruct H0.
  assert (~A).
  red.
  intro.
  apply H in H2.
  apply H2 in H0.
  assumption.
  assumption.
  assert (B /\ ~A).
  split.
  assumption.
  assumption.
  apply H0 in H3.
  absurd (A).
  assumption.
  assumption.
Qed.

Theorem Thm2A: ~ exists A, forall x, x ∈ A.
Proof.
  red.
  intros H1.
  destruct H1.
  pose (H2 := separ x (fun y => y ∉ y)).
  destruct H2.
  destruct (H0 x0).
  specialize (H x0).
  apply (two (x0 ∈ x0) (x0 ∈ x)).

  split. assumption. 
  split. assumption. assumption.
Qed.

Theorem Thm2B: forall (A: set), A <> ∅ -> exists (B: set), forall (x: set), (x ∈ B -> (forall y, y ∈ A /\ x ∈ y)).

Proof.
  intros.
  pose (H1 := at_least A H).
  destruct (H1).
  intro_subset A (fun x => forall y, y ∈ A /\ x ∈ y).
  exists x0.
  intro.
  specialize (H2 x1).
  intro.
  destruct H2.
  destruct H2.
  assumption.
  assumption.
(*  intros.*)
(*  assert (exists a, a ∈ A).*)
(*  assert (exists (a: set), a ∈ A).*)
(*  apply (at_least).*)
(*  assumption.*)
(*  assumption.*)
(*  destruct (H0).*)
(*  assert (exists B, forall x0, (x0 ∈ B <-> x0 ∈ A /\ (forall y, y ∈ A /\ x0 ∈ y))).*)
(*  apply (separ).*)
(*  assert (exists B, forall x0, (x0 ∈ B -> (forall y, y ∈ A /\ x0 ∈ y))).*)
(*  destruct H2.*)
(*  exists x0.*)
(*  intro.*)
(*  specialize (H2 x1).*)
(*  destruct H2.*)
(*  intro.*)
(*  apply H2 in H4.*)
(*  destruct H4.*)
(*  assumption.*)
(*  assumption.*)
Qed.

(* maybe useless? *)
(*Definition inter_builder (A: set)(P: Prop)  := proj1_exists (Thm2B A P).*)

(*Notation "∩" := inter_builder (at level 80).*)

Lemma inter_two_lemma: forall A B, exists C, forall x, x ∈ C <-> (x ∈ A /\ x ∈ B).
Proof.
  intros.
  intro_subset A (fun x => x ∈ B).
  exists x.
  apply H.
Qed.

Definition inter_two (A: set) (B: set) := proj1_exists(inter_two_lemma A B).
Notation "A ∩ B" := (inter_two A B)(at level 10).
Axiom union: forall A: set, exists B: set, forall x: set, x ∈ B <-> (exists a, a ∈ A /\ x ∈ a).

Definition union_builder (A : set) := proj1_exists (union A).

Notation "∪" := union_builder (at level 80).

Definition union_two (A: set) (B: set) := union_builder (pair_builder A B)
.

Notation "A ∪ B" := (union_two A B) (at level 79).
Ltac intro_union A :=
  pose (G := union A); destruct G.

Lemma sub_sub_sub: forall A B C, A ⊆ B -> B ⊆ C -> A ⊆ C.
Proof.
  intros.
  pose (H2 := H a).
  pose (H3 := H0 a).
  apply H3.
  apply H2.
  apply H1.
Qed.

Lemma inter_in1: forall A B, A ∩ B ⊆ A.
Proof.
  intros.
  pose (H1 := proj2_exists(inter_two_lemma A B)).
  pose (H2 := H1 a).
  destruct H2.
  pose (H3 := H0 H).
  destruct H3.
  apply H3.
Qed.

(* Proof switch and use rewrite*)
Lemma inter_in2: forall A B, A ∩ B ⊆ B.
Proof.
  intros.
  pose (H1 := proj2_exists(inter_two_lemma A B)).
  pose (H2 := H1 a).
  destruct H2.
  pose (H3 := H0 H).
  destruct H3.
  apply H4.
Qed.

Lemma sub_sub_inter: forall A B x, x ⊆ A -> x ⊆ B -> x ⊆ A ∩ B.
Proof.
  intros.
  pose (H2 := in_subset_in a x A H1 H).
  pose (H3 := in_subset_in a x B H1 H0).
  pose (H4 := proj2_exists(inter_two_lemma A B)).
  pose (H5 := H4 a).
  apply H5.
  split. assumption. assumption.
Qed.

Lemma inter_sub_sub: forall A B x, x ⊆ A ∩ B -> x ⊆ A /\ x ⊆ B.
Proof.
  intros.
  split.
  pose (H1 := inter_in1 A B).
  pose (H2 := sub_sub_sub x (A ∩ B) A H H1).
  apply H2.
 
  pose (H1 := inter_in2 A B).
  pose (H2 := sub_sub_sub x (A ∩ B) B H H1).
  apply H2.
Qed.

Lemma W: forall x y P , x ∈ { k ∈ y | P k } -> P x.
Proof.
  intros.
  pose (a:= proj2_exists ( separ y P )).
  pose (b := a x).
  destruct b.
  pose (c := H0 H).
  destruct c.
  assumption.
Qed.

Example ex3: forall A, forall a, a ∈ A -> a ⊆ ∪A.
Proof.
  intros.
  pose (C := proj2_exists (union A)).
  pose (b := C a0).
  destruct b.
  apply H2.
  exists a.
  split. assumption. assumption.
Qed.

(*Lemma ex3_rev: forall A, forall a*)

Lemma union_rev: forall x A, x ∈ (∪A) -> (exists a, a ∈ A /\ x ∈ a).
Proof.
  intros.
  pose (H1 := proj2_exists (union A)).
  pose (H2 := H1 x).
  destruct H2.
  pose (H3 := H0 H).
  apply H0.
  apply H.
Qed.

Example ex4: forall A B, A ⊆ B -> ∪A ⊆ ∪B.
Proof.
  intros.
  pose (b := proj2_exists (union B)).
  pose (c := b a).
  apply c.
  
  pose (d := proj2_exists (union A)).
  pose (e := d a).
  pose (f := union_rev a A H0).
  destruct f.
  exists x.
  destruct H1.
  split.
  apply H.
  apply H1.
  apply H2.
Qed.
  
Example ex5: forall A B, (forall x, x ∈ A -> x ⊆ B) -> (∪A) ⊆ B.
Proof.
  intros.
  pose (b := union_rev a A H0).
  destruct b.
  destruct H1.
  pose (c := H x H1).
  pose (d := c a H2).
  apply d.
Qed.

Example ex6a: forall A, ∪(P(A)) = A.
Proof.
  intros.
  apply subset_eq.
  split.
  apply (ex5).
  apply (power_sub).

  intros.
  pose (H1 := proj2_exists (union (P(A)) )).
  pose (H2 := H1 a).
  destruct H2.
  apply H2.
  exists A.
  split.
  pose (H3 := proj2_exists (power A)).
  apply (power_in).
  apply H.
Qed.

Example ex6b: forall A, A ⊆ P(∪A).
Proof.
  intros.
  pose (H1 := proj2_exists(power (∪A))).
  pose (H2 := H1 a).
  destruct H2.
  apply H2.
  apply ex3.
  apply H.
Qed.

Example ex7a: forall A B, (P(A) ∩ P(B)) = P(A ∩ B).
Proof.
  intros.
  apply subset_eq.
  split.

  intros.
  pose (H1 := proj2_exists (power (A ∩ B))).
  pose (H2 := H1 a).
  apply H2.
  intros. 
  pose (H3 := proj2_exists (inter_two_lemma A B)).
  pose (H4 := H3 a0).
  destruct H4.
  apply (sub_sub_inter A B a0).
  apply H5.
  pose (H6 := H2 H).
  pose (H6 := in_subset_in H0 
  apply H5.
  split.

  destruct H4.
  apply H2.

  
  

Definiti in_union x A := (exists b, b ∈ A /\ x ∈ b).


Notation "B = {A|P}" := (forall s, s ∈ B <-> s ∈ A /\ P s) (at level 70).




Definition is_sep (test: set->Prop) x y := forall u, u ∈ y <-> u ∈ x /\ test u.
Theorem Thm2AS: ~ exists A, forall x, x ∈ A.
Proof.
  red.
  intros.
  destruct H.
  pose ({x ∈ x | x ∉ x})..


