(* Only two objects in the alphabet of ZFC *)
Parameter set    : Prop.
Parameter set_in : set -> set -> Prop.
(* For curry it *)
Definition set_in2 (x: set) (y: set) := set_in y x.
Notation   "x ∈ y"                  := (set_in x y)    (at level 65, no associativity).
Notation   "x ∉  y"                  := (~(set_in x y)) (at level 65, no associativity).
Definition subset  (A: set) (B: set) := forall x: set, x ∈ A -> x ∈ B.
Infix      "⊆"                      := (subset)        (at level 65, no associativity).
(*----------------------------------------------------------------------------*)

(* Some function for build set object. *) 
(* Get that existed set. *) 
Definition extract_set :=
  fun {P: set -> Prop} (e: (exists x: set, P x))
    => let (a, _) := e in a.
(* Extract the set with its property *)
Definition extract_set_property :=
  fun {P: set -> Prop} (e: (exists x: set, P x))
    => let (a, b) as e0 return (P (extract_set e0)) := e in b.
(* Ltac templete *)
(* Ltac intro_xxx *)
(*   Intro the set which sat. that axiom *)
(* Ltac elmn_xxx *)
(*   If the set is the element of some set, expand its propety *)
(*----------------------------------------------------------------------------*)

(* Axiom of Extensionality *)
Axiom ax_exten: forall A B: set, (forall x: set, x ∈ A <-> x ∈ B) -> A = B.
(*----------------------------------------------------------------------------*)

(* Axiom of Empty Set *)
(* NOT requirement, maybe discard later. *)
Axiom ax_empty: exists A: set, forall x: set, x ∉  A.
Definition emptyset_ctor := extract_set(ax_empty).
Notation "∅" := emptyset_ctor.
Ltac intro_empty :=
  let G := fresh in
    pose (G := ax_empty); 
    destruct G.
(*----------------------------------------------------------------------------*)

(* Axiom of Pairing *)
(* Not requirement? with axiom \of replacement *)
Axiom ax_pair: forall A B: set, exists C: set, forall x: set, 
  x ∈ C <-> (x = A \/ x = B).
Definition pair_ctor (A: set) (B: set) := extract_set (ax_pair A B).
Definition singleton (A: set)          := pair_ctor A A.
Ltac intro_pair A B :=
  let G := fresh in
    pose (G := ax_pair A B); 
    destruct G.
Ltac elmn_pair elmn A B :=
  let G1 := fresh in
    let G2 := fresh in
      pose (G1 := extract_set_property(ax_pair A B)); 
      pose (G2 := G1 elmn);
      destruct G2.
(*----------------------------------------------------------------------------*)

(* Axiom of Union *)
Axiom ax_union: forall A: set, exists B: set, forall x: set, 
  x ∈ B <-> (exists a, a ∈ A /\ x ∈ a).
Definition union_ctor (A: set) := extract_set (ax_union A).
Notation "∪( A )" := (union_ctor A) (at level 60, no associativity).
Ltac intro_union A :=
  let G := fresh in
    pose (G := ax_union A);
    destruct G.
Ltac elmn_union elmn A :=
  let G1 := fresh in
    let G2 := fresh in
      pose (G1 := extract_set_property(ax_union A)); 
      pose (G2 := G1 elmn);
      destruct G2.
(*----------------------------------------------------------------------------*)


(* Union of two, not axiom but useful *)
Theorem thm_union2: forall A B: set, exists C: set, forall x: set,
  x ∈ C <-> x ∈ A \/ x ∈ B.
Proof.
  intros A B.
  destruct (ax_pair A B) as [x P1].
  destruct (ax_union x) as [y P2].
  exists y.
  intro z.
  destruct (P2 z) as [P3 _].
  split.
  + intro P4.
    destruct (P3 P4) as [w [P5 P6]].
    destruct (P1 w ) as [P7 _].
    destruct (P7 P5) as [P8|P8].
    - left.  rewrite <- P8. apply P6.
    - right. rewrite <- P8. apply P6.
  + intro P4.
    apply (P2 z).
    destruct P4 as [P4|P4].
    - exists A.
      split.
      * apply (P1 A). left. reflexivity.
      * apply P4.
    - exists B.
      split.
      * apply (P1 B). right. reflexivity.
      * apply P4.
Qed.

Definition union2_ctor (A: set) (B: set) := extract_set (thm_union2 A B).
Notation "A ∪ B" := (union2_ctor A B) (at level 60, no associativity).
Ltac intro_union2 A B :=
  let G := fresh in
    pose (G := thm_union2 A B);
    destruct G.
Ltac elmn_union2 elmn A B :=
  let G1 := fresh in
    let G2 := fresh in
      pose (G1 := extract_set_property(thm_union2 A B)); 
      pose (G2 := G1 elmn);
      destruct G2.
Notation "{ x , .. , y }" := 
  (union2_ctor (singleton(x)) .. (union2_ctor (singleton(y)) ∅) ..) 
  (at level 60).
(*----------------------------------------------------------------------------*)

(* Axiom of Power Set *)
Axiom ax_power: forall A: set, exists B: set, forall x: set, x ∈ B <-> x ⊆ A. 
Definition power_ctor (A: set) := extract_set (ax_power A).
Notation "𝒫( x )" := (power_ctor x) (at level 60, no associativity).
Ltac intro_power A :=
  let G := fresh in
    pose (G := ax_power A); destruct G.
Ltac elmn_power elmn A :=
  let G1 := fresh in
    let G2 := fresh in
      pose (G1 := extract_set_property(ax_power A)); 
      pose (G2 := G1 elmn); 
      destruct G2.
(*----------------------------------------------------------------------------*)

(* Axiom Schema of Subset *)
Axiom ax_subset: forall P: set -> Prop, forall A: set, 
  exists B: set, forall x: set, x ∈ B <-> x ∈ A /\ P x.
Definition subset_ctor (P: set -> Prop) (x: set) := extract_set(ax_subset P x).
Notation "{ x ∈ y | P }" := (subset_ctor (fun x=>P) y) (at level 60, no associativity).
Ltac intro_subset P A :=
  let G := fresh in
    pose (G := ax_subset P A);
    destruct G.
Ltac elmn_subset elmn P A :=
  let G1 := fresh in
    let G2 := fresh in
      pose (G1 := extract_set_property(ax_subset P A)); 
      pose (G2 := G1 elmn);
      destruct G2.
(*----------------------------------------------------------------------------*)


(* Intersection, not axiom but useful *)
Theorem thm_inter2: forall A B: set, exists C: set, 
  forall x, x ∈ C <-> (x ∈ A /\ x ∈ B).
Proof.
  intros A B.
  destruct (ax_subset (fun x => x ∈ B) A) as [x P].
  exists x.
  apply P.
Qed.
Definition inter2_ctor (A: set) (B: set) := extract_set(thm_inter2 A B).
Notation "A ∩ B" := (inter2_ctor A B) (at level 60, no associativity).
Ltac intro_inter2 A B :=
  let G := fresh in
    pose (G := thm_inter2 A B);
    destruct G.
Ltac elmn_inter2 elmn A B :=
  let G1 := fresh in
    let G2 := fresh in
      pose (G1 := extract_set_property(thm_inter2 A B)); 
      pose (G2 := G1 elmn);
      destruct G2.
(*----------------------------------------------------------------------------*)

