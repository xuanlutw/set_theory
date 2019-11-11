Require Import logic.
Require Import axiom.
Require Import basic.

(* order pair *)
Definition opair (A: set) (B: set) := {{A}, {A, B}}.
Notation "⟨ A , B ⟩" := (opair A B) (at level 60).

Lemma in_opair_elim: forall A B x, x ∈ ⟨A, B⟩ -> x = {A} \/ x = {A, B}.
Proof.
  intros A B x P1.
  apply (in_pair_equal ({A}) ({A, B}) x P1).
Qed.

(* 3A *)
Theorem opair_equal_intro: forall A B C D, (A = C) /\ (B = D) -> ⟨A, B⟩ = ⟨C, D⟩.
Proof.
  intros A B C D P1.
  destruct P1 as [P2 P3].
  rewrite P2.
  rewrite P3.
  reflexivity.
Qed.

Theorem opair_equal_elim: forall A B C D, ⟨A, B⟩ = ⟨C, D⟩ -> (A = C) /\ (B = D).
Proof.
  intros A B C D P1.
  destruct (pair_pair_equal_1 ({A}) ({A, B}) ({C}) ({C, D}) P1) as [P2|P2].
  + symmetry in P1.
    destruct (pair_pair_equal_2 ({C}) ({C, D}) ({A}) ({A, B}) P1) as [P3|P3].
    - split.
      * apply (singleton_equal A C P2).
      * symmetry in P1.
        destruct (pair_pair_equal_2 ({A}) ({A, B}) ({C}) ({C, D}) P1) as [P4|P4].
        { symmetry in P3.
          rewrite <- (singleton_pair_equal_2 A C D P3).
          symmetry in P4.
          symmetry.
          apply (singleton_pair_equal_3 C A B P4). }
        { destruct (pair_pair_equal_2 A B C D P4) as [P5|P5].
          { rewrite P5.
            symmetry in P3.
            apply (singleton_pair_equal_3 A C D P3). }
          { apply P5. } }
    - split.
      * apply (singleton_equal A C P2).
      * destruct (pair_pair_equal_2 C D A B P3) as [P4|P4].
        { symmetry in P3.
          destruct (pair_pair_equal_2 A B C D P3) as [P5|P5].
          { rewrite P5.
            rewrite P4.
            symmetry.
            apply (singleton_equal A C P2). }
          { apply P5. } }
        { symmetry.
          apply P4. }
  + split.
    - apply (singleton_pair_equal_1 A C D P2).
    - destruct (pair_pair_equal_2 ({A}) ({A, B}) ({C}) ({C, D}) P1) as [P3|P3].
      * rewrite <- (singleton_pair_equal_2 A C D P2).
        symmetry.
        symmetry in P3.
        apply (singleton_pair_equal_3 C A B P3).
      * destruct (pair_pair_equal_2 A B C D P3) as [P4|P4].
        { rewrite P4.
          apply (singleton_pair_equal_3 A C D P2). }
        { apply P4. }
Qed.
          
(* 3B *)
Lemma opair_superset: forall A B C, A ∈ C -> B ∈ C -> ⟨A, B⟩ ∈ 𝒫(𝒫(C)).
Proof.
  intros A B C P1 P2.
  apply (subset_in_power).
  intros x P3.
  apply (subset_in_power).
  intros y P4.
  destruct (in_pair_equal ({A}) ({A, B}) x P3) as [P5|P5].
  + rewrite P5 in P4.
    rewrite (in_singleton_equal A y P4) in P1.
    apply P1.
  + rewrite P5 in P4.
    destruct (in_pair_equal A B y P4) as [P6|P6].
    - rewrite P6.
      apply P1.
    - rewrite P6.
      apply P2.
Qed.

Definition in_cp s A B:=
  exists a b, a ∈ A /\ b ∈ B /\ s = ⟨a, b⟩.

(* Cartesion Product *)
Definition cp (A: set) (B: set) :=
  (subset_ctor 
    (fun s => in_cp s A B)
    (𝒫(𝒫(A ∪ B)))).

Lemma cp_intro: forall A B x y, x ∈ A -> y ∈ B -> ⟨x, y⟩ ∈ cp A B.
Proof.
  intros A B x y P1 P2.
  destruct ((extract_set_property 
    (ax_subset 
      (fun S => in_cp S A B) 
      (𝒫(𝒫(A ∪ B))))) (⟨x, y⟩)) as [_ P3].
  apply P3.
  split.
  + apply opair_superset.
    - apply (in_in_union2_1 _ _ _ P1).
    - apply (in_in_union2_2 _ _ _ P2).
  + exists x.
    exists y.
    split.
    - apply P1.
    - split.
      * apply P2.
      * reflexivity.
Qed.

Lemma cp_elim: forall A B x, x ∈ cp A B -> in_cp x A B.
Proof.
  intros A B x P1.
  destruct ((extract_set_property 
    (ax_subset 
      (fun S => in_cp S A B) 
      (𝒫(𝒫(A ∪ B))))) x) as [P2 _].
  destruct (P2 P1) as [_ P3].
  apply P3.
Qed.

Definition relation (R: set) :=
  forall r, r ∈ R -> exists a b, r = ⟨a, b⟩. 

Definition in_domain (x: set) (R: set) :=
  exists y, ⟨x, y⟩ ∈ R.
Definition domain (A: set) := 
  subset_ctor (fun x => (in_domain x A)) (∪(∪(A))).
Notation "dom( A )" := (domain A) (at level 60, no associativity).

Definition in_range (y: set) (R: set) :=
  exists x, ⟨x, y⟩ ∈ R.
Definition range (A: set) := 
  subset_ctor (fun x => (in_range x A)) (∪(∪(A))).
Notation "ran( A )" := (range A) (at level 60, no associativity).

Definition filed (R:set) :=
  domain R ∪range R.
Notation "fld( A )" := (filed A) (at level 60, no associativity).

(* 3D *)
Lemma domain_superset: forall A x, in_domain x A -> x ∈ ∪(∪(A)).
Proof.
  intros A x P1.
  destruct P1 as [y P1].
  apply in_in_union.
  exists ({x, y}).
  split.
  + apply in_in_union.
    exists (⟨x, y⟩).
    split.
    - apply P1.
    - apply in_pair_2.
  + apply in_pair_1.
Qed.

Lemma range_superset: forall A y, in_range y A -> y ∈ ∪(∪(A)).
Proof.
  intros A y P1.
  destruct P1 as [x P1].
  apply in_in_union.
  exists ({x, y}).
  split.
  + apply in_in_union.
    exists (⟨x, y⟩).
    split.
    - apply P1.
    - apply in_pair_2.
  + apply in_pair_2.
Qed.

Lemma domain_intro: forall R x, in_domain x R -> x ∈ dom(R).
Proof.
  intros R x P1.
  destruct P1 as [y P1].
  destruct (extract_set_property 
    (ax_subset (fun x => (in_domain x R)) (∪(∪(R)))) 
    x) as [_ P2].
  apply P2.
  split.
  + apply domain_superset.
    exists y.
    apply P1.
  + exists y.
    apply P1.
Qed.

Lemma domain_elim: forall R x, x ∈ dom(R) -> in_domain x R.
Proof.
  intros R x P1.
  destruct (extract_set_property 
    (ax_subset (fun x => (in_domain x R)) (∪(∪(R)))) 
    x) as [P2 _].
  apply P2.
  apply P1.
Qed.

Lemma range_intro: forall R y, in_range y R -> y ∈ ran(R).
Proof.
  intros R y P1.
  destruct P1 as [x P1].
  destruct (extract_set_property 
    (ax_subset (fun x => (in_range x R)) (∪(∪(R)))) 
    y) as [_ P2].
  apply P2.
  split.
  + apply range_superset.
    exists x.
    apply P1.
  + exists x.
    apply P1.
Qed.

Lemma range_elim: forall R y, y ∈ ran(R) -> in_range y R.
Proof.
  intros R y P1.
  destruct (extract_set_property 
    (ax_subset (fun x => (in_range x R)) (∪(∪(R)))) 
    y) as [P2 _].
  apply P2.
  apply P1.
Qed.

(* Skip n-ary *)

Definition function (F: set) := 
  (relation F) /\ (forall a b1 b2, ⟨a, b1⟩ ∈ F /\ ⟨a, b2⟩ ∈ F -> b1 = b2).

Lemma fun_val_thm: forall F x, exists y, function F -> x ∈ dom(F) -> 
  (⟨x, y⟩ ∈ F /\ (forall y2, ⟨x, y2⟩ ∈ F -> y = y2)).
Proof.
  intros F x.
  destruct (LEM (x ∈ dom(F))) as [P1|P1].
  + destruct (domain_elim _ _ P1) as [y P2].
    exists y.
    intros P3 P4.
    split.
    - apply P2.
    - intros y2 P5.
      destruct P3 as [_ P3].
      apply (P3 x y y2 (conj P2 P5)).
  + exists x.
    intros _ P2.
    contradiction.
Qed.

Definition fun_val (F:set) (x:set) :=
  extract_set (fun_val_thm F x).

Theorem fun_val_elim: forall F x y, y = fun_val F x -> function F -> x ∈ dom(F) ->
  (⟨x, y⟩ ∈ F /\ (forall y2, ⟨x, y2⟩ ∈ F -> y = y2)).
Proof.
  intros F x y P1.
  rewrite P1.
  apply (extract_set_property (fun_val_thm F x)).
Qed.

Theorem fun_val_intro: forall F x y, function F -> x ∈ dom(F) -> ⟨x, y⟩ ∈ F -> 
  y = fun_val F x.
Proof.
  intros F x y P1 P2 P3.
  destruct (extract_set_property (fun_val_thm F x) P1 P2) as [_ P4].
  rewrite <- (P4 y P3). 
  reflexivity.
Qed.

Lemma fun_val_basic: forall F x, function F -> x ∈ dom(F) -> ⟨x, fun_val F x⟩ ∈ F.
Proof.
  intros F x P1 P2.
  destruct (extract_set_property (fun_val_thm F x) P1 P2) as [P3 _].
  apply P3.
Qed.

Lemma fun_val_range: forall F x, function F -> x ∈ dom(F) -> 
  fun_val F x ∈ ran(F).
Proof.
  intros F x P1 P2.
  apply range_intro.
  exists x.
  apply (fun_val_basic F x P1 P2).
Qed.

Definition single_rooted (R: set) :=
  (forall a1 a2 b, ⟨a1, b⟩ ∈ R /\ ⟨a2, b⟩ ∈ R -> a1 = a2).

Definition one_to_one (F: set) :=
  (function F) /\ (single_rooted F). 

Definition in_inverse (x: set) (R: set) :=
  (exists a b, ⟨a, b⟩ ∈ R /\ x = ⟨b, a⟩).
Definition inverse (R: set) := 
  subset_ctor (fun x => (in_inverse x R)) (cp (ran(R)) (dom(R))).

Lemma inverse_superset: forall x R, in_inverse x R -> x ∈ cp (ran(R)) (dom(R)).
Proof.
  intros x R P1.
  destruct P1 as [a [b [P1 P2]]].
  rewrite P2.
  apply cp_intro.
  + apply range_intro.
    exists a.
    apply P1.
  + apply domain_intro.
    exists b.
    apply P1.
Qed.

Theorem inverse_intro: forall x y R, ⟨x, y⟩ ∈ R -> ⟨y, x⟩ ∈ inverse R.
Proof.
  intros x y R P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_inverse s R) 
      (cp (ran(R)) (dom(R)))) (⟨y, x⟩)) as [_ P2].
  apply P2.
  assert (in_inverse (⟨y, x⟩) R) as P3.
  { exists x.
    exists y.
    split.
    + apply P1.
    + reflexivity. }
  split.
  + apply (inverse_superset _ _ P3).
  + apply P3.
Qed.

Lemma inverse_elim: forall x y R, ⟨x, y⟩ ∈ inverse R -> ⟨y, x⟩ ∈ R.
Proof.
  intros x y R P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_inverse s R) 
      (cp (ran(R)) (dom(R)))) (⟨x, y⟩)) as [P2 _].
  destruct (P2 P1) as [_ [a [b [P3 P4]]]].
  destruct (opair_equal_elim _ _ _ _ P4) as [P5 P6].
  rewrite P5.
  rewrite P6.
  apply P3.
Qed.

Definition in_composition (x: set) (F: set) (G: set) :=
  (exists a b c, ⟨a, b⟩ ∈ F /\ ⟨b, c⟩ ∈ G /\ x = ⟨a, c⟩).
Definition composition (F: set) (G: set) := 
  subset_ctor (fun x => (in_composition x F G)) (cp (dom(F)) (ran(G))).
Lemma composition_superset: forall x F G, in_composition x F G -> 
  x ∈ cp (dom(F)) (ran(G)).
Proof.
  intros x F G P1.
  destruct P1 as [a [b [c [P1 [P2 P3]]]]].
  rewrite P3.
  apply cp_intro.
  + apply domain_intro.
    exists b.
    apply P1.
  + apply range_intro.
    exists b.
    apply P2.
Qed.

Theorem composition_is_relation: forall F G, relation(composition F G).
Proof.
  intros F G r P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_composition s F G) 
      (cp (dom(F)) (ran(G)))) r) as [P2 _].
  destruct (P2 P1) as [P3 _].
  destruct (cp_elim _ _ _ P3) as [a [b [_ [_ P4]]]].
  exists a.
  exists b.
  apply P4.
Qed.

Theorem composition_intro: forall x z F G, (exists y, ⟨x, y⟩ ∈ F /\ ⟨y, z⟩ ∈ G) -> 
  ⟨x, z⟩ ∈ composition F G.
Proof.
  intros x z F G P1.
  destruct P1 as [y [P1 P2]].
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_composition s F G) 
      (cp (dom(F)) (ran(G)))) (⟨x, z⟩)) as [_ P3].
  apply P3.
  assert (in_composition (⟨x, z⟩) F G) as P4.
  { exists x.
    exists y.
    exists z.
    split.
    + apply P1.
    + split. 
      - apply P2. 
      - reflexivity. }
  split.
  + apply (composition_superset _ _ _ P4).
  + apply P4.
Qed.

Lemma composition_elim: forall x z F G, ⟨x, z⟩ ∈ composition F G -> 
  (exists y, ⟨x, y⟩ ∈ F /\ ⟨y, z⟩ ∈ G).
Proof.
  intros x z F G P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_composition s F G) 
      (cp (dom(F)) (ran(G)))) (⟨x, z⟩)) as [P2 _].
  destruct (P2 P1) as [_ [a [b [c [P3 [P4 P5]]]]]].
  destruct (opair_equal_elim _ _ _ _ P5) as [P6 P7].
  exists b.
  split.
  + rewrite P6.
    apply P3.
  + rewrite P7.
    apply P4.
Qed.

Definition in_restriction (x: set) (F: set) (A: set) :=
  (exists a b, ⟨a, b⟩ ∈ F /\ x = ⟨a, b⟩ /\ a ∈ A).
Definition restriction (F: set) (A: set) := 
  subset_ctor (fun x => (in_restriction x F A)) F.

Theorem restriction_intro: forall x y F A, ⟨x, y⟩ ∈ F -> x ∈ A -> 
  ⟨x, y⟩ ∈ restriction F A.
Proof.
  intros x y F A P1 P2.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_restriction s F A) F) 
    (⟨x, y⟩)) as [_ P3].
  apply P3.
  split.
  + apply P1.
  + exists x.
    exists y.
    split.
    - apply P1.
    - split.
      * reflexivity. 
      * apply P2.
Qed.

Lemma restriction_elim: forall x y F A, ⟨x, y⟩ ∈ restriction F A -> 
  ⟨x, y⟩ ∈ F /\ x ∈ A.
Proof.
  intros x y F A P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_restriction s F A) F) 
    (⟨x, y⟩)) as [P2 _].
  destruct (P2 P1) as [P3 [a [b [_ [P4 P5]]]]].
  destruct (opair_equal_elim _ _ _ _ P4) as [P6 _].
  split.
  + apply P3.
  + rewrite P6.
    apply P5.
Qed.

Definition image (F: set) (A: set) := 
  ran(restriction F A).

Theorem image_intro: forall y F A, (exists x, ⟨x, y⟩ ∈ F /\ x ∈ A) -> y ∈ image F A.
Proof.
  intros y F A P1.
  destruct P1 as [x [P1 P2]].
  apply range_intro.
  exists x.
  apply restriction_intro.
  + apply P1.
  + apply P2.
Qed.

Lemma image_elim: forall y F A, y ∈ image F A -> (exists x, ⟨x, y⟩ ∈ F /\ x ∈ A).
Proof.
  intros y F A P1.
  destruct (range_elim _ _ P1) as [x P2].
  destruct (restriction_elim _ _ _ _ P2) as [P3 P4].
  exists x.
  split.
  + apply P3.
  + apply P4.
Qed.

(* 3F *)
Theorem inverse_domain: forall F, dom(inverse F) = ran(F).
Proof.
  intros F.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (domain_elim _ _ P1) as [y P2].
    apply range_intro.
    exists y.
    apply (inverse_elim _ _ _ P2).
  + intros P1.
    destruct (range_elim _ _ P1) as [y P2].
    apply domain_intro.
    exists y.
    apply (inverse_intro _ _ _ P2).
Qed.
    
Theorem inverse_range: forall F, ran(inverse F) = dom(F).
Proof.
  intros F.
  apply ax_exten.
  intros x.
  split.
  + intros P1.
    destruct (range_elim _ _ P1) as [y P2].
    apply domain_intro.
    exists y.
    apply (inverse_elim _ _ _ P2).
  + intros P1.
    destruct (domain_elim _ _ P1) as [y P2].
    apply range_intro.
    exists y.
    apply (inverse_intro _ _ _ P2).
Qed.

Theorem inverse_is_relation: forall R, relation (inverse R).
Proof.
  intros R x P1.
  destruct (extract_set_property 
    (ax_subset 
      (fun s => in_inverse s R) 
      (cp (ran(R)) (dom(R)))) x) as [P2 _].
  destruct (P2 P1) as [_ [a [b [P3 P4]]]].
  exists b.
  exists a.
  apply P4.
Qed.

Theorem inverse_inverse: forall F, relation F -> inverse (inverse F) = F.
Proof.
  intros F P1.
  apply ax_exten.
  intros x.
  split.
  + intros P2.
    destruct ((inverse_is_relation (inverse F)) x P2) as [a [b P3]].
    rewrite P3.
    apply inverse_elim.
    apply inverse_elim.
    rewrite <- P3.
    apply P2.
  + intros P2.
    destruct (P1 x P2) as [a [b P3]].
    rewrite P3.
    apply inverse_intro.
    apply inverse_intro.
    rewrite <- P3.
    apply P2.
Qed.

(* 3F *)
Lemma inverse_function: forall F, single_rooted F <-> function (inverse F).
Proof.
  intros F.
  split.
  + intros P1.
    split.
    - intros x P2.
      destruct (inverse_is_relation F x P2) as [a [b P3]].
      exists a.
      exists b.
      apply P3.
    - intros a b1 b2 P2.
      destruct P2 as [P2 P3].
      apply (P1 b1 b2 a).
      split.
      * apply (inverse_elim _ _ _ P2).
      * apply (inverse_elim _ _ _ P3).
  + intros P1.
    intros a1 a2 b P2.
    destruct P2 as [P2 P3].
    destruct P1 as [_ P1].
    apply (P1 b a1 a2).
    split.
    - apply (inverse_intro _ _ _ P2).
    - apply (inverse_intro _ _ _ P3).
Qed.

Lemma function_inverse: forall F, relation F -> (function F <-> single_rooted(inverse F)).
Proof.
  intros F P1.
  split.
  + intros P2 a1 a2 b P3.
    destruct P2 as [_ P2].
    destruct P3 as [P3 P4].
    apply (P2 b a1 a2).
    split.
    - apply (inverse_elim _ _ _ P3). 
    - apply (inverse_elim _ _ _ P4).
  + intros P2.
    split.
    - apply P1.
    - intros a b1 b2 P3.
      destruct P3 as [P3 P4].
      apply (P2 b1 b2 a).
      split.
      * apply (inverse_intro _ _ _ P3).
      * apply (inverse_intro _ _ _ P4).
Qed.

(* 3G *)
Lemma inverse_function_exist_1: forall F, one_to_one F -> 
  (forall x, x ∈ dom(F) -> (fun_val (inverse F) (fun_val F x)) = x).
Proof.
  intros F P1 x P2.
  symmetry.
  apply fun_val_intro.
  + destruct P1 as [_ P1].
    destruct (inverse_function F) as [P3 _].
    apply (P3 P1).
  + rewrite inverse_domain.
    apply range_intro.
    exists x.
    destruct P1 as [P1 _].
    apply (fun_val_basic _ _ P1 P2).
  + apply inverse_intro.
    destruct P1 as [P1 _].
    apply (fun_val_basic _ _ P1 P2).
Qed.

Lemma inverse_function_exist_2: forall F, one_to_one F -> 
  (forall x, x ∈ ran(F) -> (fun_val F (fun_val (inverse F) x)) = x).
Proof.
  intros F P1 x P2.
  symmetry.
  apply fun_val_intro.
  + destruct P1 as [P1 _].
    apply P1.
  + apply domain_intro.
    exists x.
    apply inverse_elim.
    destruct P1 as [_ P1].
    destruct (inverse_function F) as [P3 _].
    rewrite <- inverse_domain in P2.
    apply (fun_val_basic _ _ (P3 P1) P2).
  + apply inverse_elim.
    destruct P1 as [_ P1].
    destruct (inverse_function F) as [P3 _].
    rewrite <- inverse_domain in P2.
    apply (fun_val_basic _ _ (P3 P1) P2).
Qed.

(* 3H *)
Lemma composition_function: forall F G, function F -> function G ->
  function (composition F G).
Proof.
  intros F G P1 P2.
  split.
  + apply composition_is_relation.
  + intros a b1 b2 [P3 P4].
    destruct (composition_elim _ _ _ _ P3) as [y1 [P5 P6]].
    destruct (composition_elim _ _ _ _ P4) as [y2 [P7 P8]].
    destruct P1 as [_ P1].
    rewrite (P1 _ _ _ (conj P5 P7)) in P6.
    destruct P2 as [_ P2].
    apply (P2 _ _ _ (conj P6 P8)).
Qed.

(* Lemma composition domain *)
Lemma composition_domain: forall F G x, function F -> function G -> 
  x ∈ dom(composition F G) -> x ∈ dom(F) /\ (fun_val F x) ∈ dom(G).
Proof.
  intros F G x P1 P2 P3.
  destruct (domain_elim _ _ P3) as [z P4].
  destruct (composition_elim _ _ _ _ P4) as [y [P5 P6]].
  split.
  + apply domain_intro.
    exists y.
    apply P5.
  + apply domain_intro.
    exists z.
    assert (x ∈ dom(F)) as P7.
    { apply domain_intro.
      exists y.
      apply P5. }
    rewrite <- (fun_val_intro _ _ _ P1 P7 P5).
    apply P6.
Qed.

Lemma composition_basic: forall F G x, function F -> function G -> 
  x ∈ dom(composition F G) -> 
  (fun_val (composition F G) x) = (fun_val G (fun_val F x)).
Proof.
  intros F G x P1 P2 P3.
  symmetry.
  apply (fun_val_intro _ _ _ (composition_function _ _ P1 P2) P3).
  apply (composition_intro).
  exists (fun_val F x).
  destruct (composition_domain _ _ _ P1 P2 P3) as [P4 P5].
  split.
  + apply (fun_val_basic _ _ P1).
    apply P4.
  + apply (fun_val_basic _ _ P2).
    apply P5.
Qed.

(* 3I *)
Theorem composition_inverse: forall F G, inverse (composition F G) =
  composition (inverse G) (inverse F).
Proof.
  intros F G.
  apply ax_exten.
  intros r.
  split.
  + intros P1.
    destruct (inverse_is_relation _ r P1) as [x [z P2]].
    rewrite P2.
    rewrite P2 in P1.
    apply composition_intro.
    destruct (composition_elim _ _ _ _ (inverse_elim _ _ _ P1)) as [y [P3 P4]].
    exists y.
    split.
    - apply (inverse_intro _ _ _ P4).
    - apply (inverse_intro _ _ _ P3).
  + intros P1.
    destruct (composition_is_relation _ _ r P1) as [x [z P2]].
    rewrite P2.
    rewrite P2 in P1.
    apply inverse_intro.
    apply composition_intro.
    destruct (composition_elim _ _ _ _ P1) as [y [P3 P4]] .
    exists y.
    split.
    - apply (inverse_elim _ _ _ P4).
    - apply (inverse_elim _ _ _ P3).
Qed.



(* TODO classify different difition *)
(* TODO intro and elim fun *)

    
