Set Warnings "-notation-overridden".

Require Import Category.Theory.
Require Import Category.Structure.Monoidal.
Require Import Category.Lib.
Require Import Category.Structure.Monoidal.Proofs.

Require Import Enriched.Category.
Require Import Enriched.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Lib.
Context {V0: Category} {V : Monoidal}.

Section Category.

Definition ehom0 {C : EnrichedCategory} x y := I ~> (ehom x y).

Definition ecompose0 {C : EnrichedCategory} {x y z} (f : ehom0 y z) (g : ehom0 x y):= (ecompose ∘ bimap f g ∘ unit_right⁻¹)%morphism.

Definition precompose {C : EnrichedCategory} {x y} (f : ehom0 x y) {z} : ehom y z ~> ehom x z := (ecompose ∘ id ⨂ f ∘ unit_right⁻¹)%morphism.

Definition postcompose {C : EnrichedCategory} {x y} (f : ehom0 x y) {z} : ehom z x ~> ehom z y := (ecompose ∘ f ⨂ id ∘ unit_left⁻¹)%morphism.

Lemma pre_post_commute {C : EnrichedCategory} {x y z w} {f : ehom0 x y} {g : ehom0 z w} : ((postcompose g) ∘ (precompose f) ≈ (precompose f) ∘ (postcompose g))%morphism.
Proof.
  unfold postcompose, precompose.
  rewrite (comp_assoc_sym _ unit_left⁻¹ _)%morphism.
  rewrite <- from_unit_left_natural.
  rewrite (comp_assoc_sym _ unit_right⁻¹ _)%morphism.
  rewrite (comp_assoc unit_right⁻¹ (ecompose ∘ g ⨂ id[ehom y z]))%morphism.
  rewrite <- from_unit_right_natural.
  normal.
  transitivity (ecompose ∘ (id ⨂ ecompose ∘ g ⨂ (id[ehom y z] ⨂ f) ∘ id ⨂ unit_right⁻¹) ∘ unit_left⁻¹)%morphism.
  do 2 rewrite <- bimap_comp.
  normal.
  reflexivity.
  transitivity (ecompose ∘ (ecompose ⨂ id ∘ (g ⨂ id[ehom y z]) ⨂ f) ∘ unit_right⁻¹ ∘ unit_left⁻¹)%morphism.
  Focus 2.
  rewrite <- bimap_comp.
  normal.
  reflexivity.
  repeat rewrite comp_assoc.
  rewrite ecomp_assoc.
  repeat rewrite comp_assoc_sym.
  do 2 f_equiv.
  repeat rewrite comp_assoc.
  f_equiv.
  rewrite <- to_tensor_assoc_natural.
  repeat rewrite comp_assoc_sym.
  f_equiv.
  transitivity (id ⨂ unit_right⁻¹ ∘ (id ⨂ unit_right : I ⨂ (ehom y z ⨂ I) ~> I ⨂ ehom y z) ∘ tensor_assoc ∘ unit_right⁻¹)%morphism.
  transitivity ((id ⨂ unit_right⁻¹ : I ⨂ ehom y z ~> I ⨂ (ehom y z ⨂ I)) ∘ (unit_right ∘ unit_right⁻¹))%morphism.
  rewrite iso_to_from.
  normal.
  reflexivity.
  Focus 2.
  rewrite <- bimap_comp.
  rewrite iso_from_to.
  normal.
  reflexivity.
  rewrite (comp_assoc_sym (id[I] ⨂ unit_right⁻¹) (id[I] ⨂ unit_right)).
  assert (unit_right << (I ⨂ ehom y z) ⨂ I ~~> I ⨂  ehom y z >> id[I] ⨂ unit_right ∘ tensor_assoc)%morphism.
  {
    rewrite triangle_identity_right.
    rewrite comp_assoc_sym.
    rewrite iso_from_to.
    normal.
    reflexivity.
  }
  rewrite X.
  normal.
  reflexivity.
Qed.

(* TODO: give a better name *)
Lemma lib_l1 {x} : (tensor_assoc ∘ unit_right⁻¹ ⨂ id[I] ≈ id[x] ⨂ unit_right⁻¹)%morphism.
Proof.
  transitivity (id[x] ⨂ unit_right⁻¹ ∘ id ⨂ unit_right ∘ tensor_assoc ∘ unit_right⁻¹ ⨂ id[I])%morphism.
  normal.
  rewrite iso_from_to.
  normal.
  reflexivity.
  rewrite (comp_assoc_sym (id ⨂ unit_right⁻¹)).
  rewrite <- bimap_triangle_right.
  rewrite <- id_unit_right.
  normal.
  rewrite iso_to_from.
  reflexivity.
Qed.

Lemma pre_comp {C : EnrichedCategory} {x y z w} {f : ehom0 x y} {g : ehom0 y z} : (precompose (z:=w) (ecompose0 g f) ≈ precompose f ∘ precompose g)%morphism.
Proof.
  unfold precompose, ecompose0.
  rewrite (comp_assoc_sym _ unit_right⁻¹).
  rewrite <- from_unit_right_natural.
  normal.
  assert ((ecompose ∘ id[ehom z w] ⨂ g ∘ unit_right⁻¹) ⨂ f ≈ ecompose ⨂ id ∘ (id[ehom z w] ⨂ g) ⨂ f ∘ unit_right⁻¹ ⨂ id)%morphism.
  {
    normal.
    reflexivity.
  }
  rewrite X;clear X.
  repeat rewrite comp_assoc.
  rewrite ecomp_assoc.
  rewrite (comp_assoc_sym _ tensor_assoc).
  rewrite <- to_tensor_assoc_natural.
  normal.
  rewrite (comp_assoc_sym _ tensor_assoc).
  rewrite lib_l1.
  normal.
  rewrite (comp_assoc_sym _ (id ⨂ ecompose)).
  rewrite <- bimap_comp.
  normal.
  reflexivity.
Qed.

Lemma post_comp {C : EnrichedCategory} {x y z w} {f : ehom0 x y} {g : ehom0 y z} : (postcompose (z:=w) (ecompose0 g f) ≈ postcompose g ∘ postcompose f)%morphism.
Proof.
  unfold postcompose, ecompose0.
  rewrite (comp_assoc_sym _ unit_left⁻¹).
  rewrite <- from_unit_left_natural.
  normal.
  f_equiv.
  assert (g ⨂ (ecompose ∘ f ⨂ id[ehom w x] ∘ unit_left⁻¹) ≈ id ⨂ ecompose ∘ tensor_assoc ∘ (g ⨂ f) ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ unit_left⁻¹)%morphism.
  {
    rewrite (comp_assoc_sym _ tensor_assoc).
    rewrite <- to_tensor_assoc_natural.
    rewrite (comp_assoc_sym _ _ tensor_assoc⁻¹), (comp_assoc_sym _ tensor_assoc).
    rewrite iso_to_from.
    normal.
    reflexivity.
  }
  rewrite X;clear X.
  repeat rewrite comp_assoc.
  rewrite <- ecomp_assoc.
  normal.
  assert (tensor_assoc⁻¹ ∘ id[I] ⨂ unit_left⁻¹ ≈ unit_right⁻¹ ⨂ id[ehom w x])%morphism.
  {
    transitivity (unit_right⁻¹⨂ id[ehom w x] ∘ unit_right ⨂ id ∘ tensor_assoc⁻¹ ∘ id[I] ⨂ unit_left⁻¹)%morphism.
    normal.
    rewrite iso_from_to.
    normal.
    reflexivity.
    rewrite (comp_assoc_sym (unit_right⁻¹ ⨂ id)).
    rewrite <- inverse_triangle_identity.
    rewrite comp_assoc_sym.
    normal.
    rewrite iso_to_from.
    reflexivity.
  }
  rewrite (comp_assoc_sym _ tensor_assoc⁻¹).
  rewrite X.
  normal.
  reflexivity.
Qed.

Lemma pre_id {C : EnrichedCategory} {x y} : precompose eid ≈ id[ehom x y].
Proof.
  unfold precompose.
  rewrite eid_right.
  apply iso_to_from.
Qed.

Lemma post_id {C : EnrichedCategory} {x y} : postcompose eid ≈ id[ehom x y].
Proof.
  unfold postcompose.
  rewrite eid_left.
  apply iso_to_from.
Qed.

Lemma ecomp0_id_left {C : EnrichedCategory} {x y} (f : ehom0 x y) : ecompose0 eid f ≈ f.
Proof.
  unfold ecompose0.
  transitivity (ecompose ∘ eid ⨂ id ∘ id ⨂ f ∘ unit_right⁻¹)%morphism.
  rewrite (comp_assoc_sym _ (eid ⨂ id)).
  rewrite <- bimap_comp.
  normal.
  reflexivity.
  rewrite eid_left.
  rewrite <- to_unit_left_natural.
  rewrite unit_identity.
  rewrite comp_assoc_sym.
  rewrite iso_to_from.
  normal.
  reflexivity.
Qed.

Lemma ecomp0_id_right {C : EnrichedCategory} {x y} (f : ehom0 x y) : ecompose0 f eid ≈ f.
Proof.
  unfold ecompose0.
  transitivity (ecompose ∘ id ⨂ eid ∘ f ⨂ id ∘ unit_right⁻¹)%morphism.
  rewrite (comp_assoc_sym _ (id ⨂ eid)).
  rewrite <- bimap_comp.
  normal.
  reflexivity.
  rewrite eid_right.
  rewrite <- to_unit_right_natural.
  rewrite comp_assoc_sym.
  rewrite iso_to_from.
  normal.
  reflexivity.
Qed.

Lemma ecomp0_assoc {C : EnrichedCategory} {x y z w} {f : ehom0 x y} {g : ehom0 y z} {h : ehom0 z w} : ecompose0 (ecompose0 h g) f ≈ ecompose0 h (ecompose0 g f).
Proof.
  unfold ecompose0.
  f_equiv.
  transitivity (ecompose ∘ ecompose ⨂ id ∘ (h ⨂ g) ⨂ f ∘ unit_right⁻¹ ⨂ id)%morphism.
  normal.
  reflexivity.
  rewrite ecomp_assoc.
  rewrite (comp_assoc_sym _ tensor_assoc).
  rewrite <- to_tensor_assoc_natural.
  repeat rewrite comp_assoc_sym.
  rewrite lib_l1.
  normal.
  reflexivity.
Qed.

Lemma ecompose0_precompose {C : EnrichedCategory} {x y z} {f : ehom0 y z} {g : ehom0 x y} : ecompose0 f g ≈ (precompose g ∘ f)%morphism.
Proof.
  unfold ecompose0, precompose.
  rewrite (comp_assoc_sym _ _ f).
  rewrite <- from_unit_right_natural.
  rewrite comp_assoc.
  rewrite (comp_assoc_sym _ (id ⨂ g)).
  rewrite <- bimap_comp.
  normal.
  reflexivity.
Qed.

Lemma ecompose0_postcompose {C : EnrichedCategory} {x y z} {f : ehom0 y z} {g : ehom0 x y} : ecompose0 f g ≈ (postcompose f ∘ g)%morphism.
Proof.
  unfold ecompose0, postcompose.
  rewrite (comp_assoc_sym _ _ g).
  rewrite <- from_unit_left_natural.
  rewrite comp_assoc.
  rewrite (comp_assoc_sym _ _ (id ⨂ g)).
  rewrite <- bimap_comp.
  normal.
  assert (unit_right⁻¹ ≈ unit_left⁻¹).
  {
    apply (iso_epic unit_left).
    rewrite iso_from_to.
    rewrite unit_identity.
    rewrite iso_from_to.
    reflexivity.
  }
  rewrite X.
  reflexivity.
Qed.

Global Program Definition ecompose0_respects {C : EnrichedCategory} {x y z} :
  Proper (equiv ==> equiv ==> equiv) (@ecompose0 C x y z).
Proof.
  proper.
  unfold ecompose0.
  rewrite X, X0.
  reflexivity.
Qed.

End Category.

Section Functor.

Definition efmap0 {C D : EnrichedCategory} {F : C ⟶ D} (x y : C) (f : ehom0 x y) : ehom0 (F x) (F y) := (efmap ∘ f)%morphism.

Lemma efmap_comp0 {C D : EnrichedCategory} {F : C ⟶ D} (x y z : C) (f : ehom0 y z) (g : ehom0 x y) : efmap0 x z (ecompose0 f g) ≈ ecompose0 (efmap0 y z f) (efmap0 x y g).
Proof.
  unfold efmap0, ecompose0.
  normal.
  rewrite <- efmap_comp.
  normal.
  reflexivity.
Qed.

Lemma efmap_id0 {C D : EnrichedCategory} {F : C ⟶ D} (x : C) : efmap0 x x eid ≈ eid.
Proof.
  unfold efmap0.
  apply efmap_id.
Qed.

End Functor.
End Lib.