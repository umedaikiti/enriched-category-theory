Set Warnings "-notation-overridden".

Require Import Category.Theory.
Require Import Category.Structure.Monoidal.
Require Import Category.Lib.
Require Import Category.Structure.Monoidal.Proofs.

Require Import Enriched.Category.
Require Import Enriched.Functor.
Require Import Enriched.Forget.Lib.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.


Section NaturalTransformation.

Context {V0: Category} {V : Monoidal}.
Context {C D : EnrichedCategory}.
Context {F G : C ⟶ D}.

Class EnrichedTransform := {
  etransform {x} : I ~> ehom (F x) (G x);

  enaturality {x y} :
    (postcompose etransform ∘ efmap (EnrichedFunctor:=F) << ehom x y ~~> ehom (F x) (G y) >> precompose etransform ∘ efmap (EnrichedFunctor:=G))%morphism;
}.

End NaturalTransformation.

Bind Scope enriched_transform_scope with EnrichedTransform.
Delimit Scope enriched_transform_type_scope with enriched_transform_type.
Delimit Scope enriched_transform_scope with enriched_transform.
Open Scope enriched_transform_type_scope.
Open Scope enriched_transform_scope.

Notation "F ⟹ G" := (@EnrichedTransform _ _ _ _ F G)
  (at level 90, right associativity) : enriched_transform_type_scope.

Coercion etransform : EnrichedTransform >-> Funclass.

Section Equivalence.

Context {V0: Category} {V : Monoidal}.
Context {C D : EnrichedCategory}.

Program Definition enat_equiv {F G : C ⟶ D} : crelation (F ⟹ G) :=
  fun n m => ∀ A, n A ≈ m A.

Hint Unfold enat_equiv.

Global Program Definition enat_equiv_equivalence {F G : C ⟶ D} :
  Equivalence (@enat_equiv F G).
Proof.
  equivalence.
  transitivity (y A);auto.
Qed.

Global Program Instance enat_Setoid {F G : C ⟶ D} :
  Setoid (F ⟹ G) := {
  equiv := enat_equiv;
  setoid_equiv := enat_equiv_equivalence
}.

End Equivalence.

Section Compose.

Context {V0: Category} {V : Monoidal}.

Program Definition outside {C D : EnrichedCategory} {F G : C ⟶ D} (a : F ⟹ G)
 {E : EnrichedCategory} (H : E ⟶ C) : F ○ H ⟹ G ○ H := {|
  etransform := fun _ => etransform (EnrichedTransform:=a)%morphism;
|}.
Next Obligation.
  normal.
  rewrite enaturality.
  reflexivity.
Qed.

Program Definition inside {C D : EnrichedCategory} {F G : C ⟶ D} (a : F ⟹ G)
 {E : EnrichedCategory} (H : D ⟶ E) : H ○ F ⟹ H ○ G := {|
  etransform := fun _ => (efmap ∘ etransform (EnrichedTransform:=a))%morphism;
|}.
Next Obligation.
  normal.
  unfold postcompose, precompose.
  rewrite (comp_assoc_sym _ unit_left⁻¹).
  rewrite <- from_unit_left_natural.
  rewrite (comp_assoc_sym _ unit_right⁻¹).
  rewrite <- from_unit_right_natural.
  normal.
  assert ((efmap ∘ a y) ⨂ efmap << I ⨂ ehom (F x) (F y) ~~> ehom (H (F y)) (H (G y)) ⨂ ehom (H (F x)) (H (F y)) >> efmap ⨂ efmap ∘ a y ⨂ id)%morphism.
  {
    normal.
    reflexivity.
  }
  rewrite X;clear X.
  assert (efmap ⨂ (efmap ∘ a x) << ehom (G x) (G y) ⨂ I ~~> ehom (H (G x)) (H (G y)) ⨂ ehom (H (F x)) (H (G x)) >> efmap ⨂ efmap ∘ id ⨂ a x)%morphism.
  {
    normal.
    reflexivity.
  }
  rewrite X;clear X.
  repeat rewrite comp_assoc.
  do 2 rewrite efmap_comp.
  repeat rewrite comp_assoc_sym.
  f_equiv.
  repeat rewrite comp_assoc.
  fold (postcompose (a y) : ehom (F x) (F y) ~> ehom (F x) (G y)).
  fold (precompose (a x) : ehom (G x) (G y) ~> ehom (F x) (G y)).
  rewrite enaturality.
  reflexivity.
Qed.

Program Definition VerticalComposite {C D : EnrichedCategory} {F G H : C ⟶ D} (b : G ⟹ H) (a : F ⟹ G) : F ⟹ H := {|
  etransform := fun _ => ecompose0 (etransform (EnrichedTransform:=b)) (etransform (EnrichedTransform:=a));
|}.
Next Obligation.
  rewrite post_comp, pre_comp.
  rewrite comp_assoc_sym, enaturality, comp_assoc.
  rewrite pre_post_commute.
  rewrite comp_assoc_sym, enaturality, comp_assoc.
  reflexivity.
Qed.

Global Instance vert_comp_respects {C D : EnrichedCategory} {F G H : C ⟶ D} :
  Proper (equiv ==> equiv ==> equiv) (@VerticalComposite C D F G H).
Proof.
  proper.
  unfold ecompose0.
  rewrite (X A).
  rewrite (X0 A).
  reflexivity.
Qed.

Program Definition enat_id {C D : EnrichedCategory} {F : C ⟶ D} : F ⟹ F := {|
  etransform := fun _ => eid
|}.
Next Obligation.
  rewrite post_id.
  rewrite pre_id.
  reflexivity.
Qed.


Lemma vert_comp_id_right {C D : EnrichedCategory} {F G : C ⟶ D} {a : F ⟹ G} : VerticalComposite a enat_id ≈ a.
Proof.
  intro.
  simpl.
  apply ecomp0_id_right.
Qed.

Lemma vert_comp_id_left {C D : EnrichedCategory} {F G : C ⟶ D} {a : F ⟹ G} : VerticalComposite enat_id a ≈ a.
Proof.
  intro.
  simpl.
  apply ecomp0_id_left.
Qed.

Lemma vert_comp_assoc {C D : EnrichedCategory} {F G H K : C ⟶ D} (c : H  ⟹ K) (b : G  ⟹ H) (a : F ⟹ G) :
  VerticalComposite (VerticalComposite c b) a ≈ VerticalComposite c (VerticalComposite b a).
Proof.
  intro.
  simpl.
  apply ecomp0_assoc.
Qed.

Lemma inside_outside {C D E : EnrichedCategory} {F G : C ⟶ D} {H K : D ⟶ E} {a  : F ⟹ G} {b : H ⟹ K} : VerticalComposite (outside b G) (inside a H) ≈ VerticalComposite (inside a K) (outside b F).
Proof.
  intro.
  simpl.
  rewrite ecompose0_postcompose.
  rewrite ecompose0_precompose.
  normal.
  rewrite <- enaturality.
  reflexivity.
Qed.

Definition HorizontalComposite {C D E : EnrichedCategory} {F G : C ⟶ D} {H K : D ⟶ E} (b : H ⟹ K) (a  : F ⟹ G) : H ○ F ⟹ K ○ G := VerticalComposite (outside b G) (inside a H).

Lemma outside_id {C D E : EnrichedCategory} {F : C ⟶ D} {G : D ⟶ E} : outside enat_id F ≈ enat_id.
Proof.
  intro.
  simpl.
  reflexivity.
Qed.

Lemma inside_id {C D E : EnrichedCategory} {F : C ⟶ D} {G : E ⟶ C} : inside enat_id F ≈ enat_id.
Proof.
  intro.
  simpl.
  apply efmap_id.
Qed.

Lemma outside_vertical {C D E : EnrichedCategory} {F G H : C ⟶ D} {K : E ⟶ C} {a : F ⟹ G} {b : G ⟹ H} : outside (VerticalComposite b a) K ≈ VerticalComposite (outside b K) (outside a K).
Proof.
  intro.
  simpl.
  reflexivity.
Qed.

Lemma inside_vertical {C D E : EnrichedCategory} {F G H : C ⟶ D} {K : D ⟶ E} {a : F ⟹ G} {b : G ⟹ H} : inside (VerticalComposite b a) K ≈ VerticalComposite (inside b K) (inside a K).
Proof.
  intro.
  simpl.
  apply efmap_comp0.
Qed.

Lemma interchange_law {C D E : EnrichedCategory} {F G H : C ⟶ D} {K L M : D ⟶ E} {a : F ⟹ G} {b : G ⟹ H} {c : K ⟹ L} {d : L ⟹ M}
  : HorizontalComposite (VerticalComposite d c) (VerticalComposite b a) ≈ VerticalComposite (HorizontalComposite d b) (HorizontalComposite c a).

Proof.
  unfold HorizontalComposite.
  rewrite outside_vertical.
  rewrite inside_vertical.
  rewrite vert_comp_assoc.
  rewrite <- (vert_comp_assoc (outside c H)).
  rewrite inside_outside.
  repeat rewrite vert_comp_assoc.
  reflexivity.
Qed.

(*
Lemma hori_comp_id_right {C D : EnrichedCategory} {F G : C ⟶ D} {a : F ⟹ G} : HorizontalComposite a enat_id ≈ a.
*)

End Compose.

Notation "F ⊙ G" := (VerticalComposite F G) (at level 40, left associativity) : enriched_category_scope.
