Set Warnings "-notation-overridden".

Require Import Category.Theory.
Require Import Category.Structure.Monoidal.
Require Import Category.Lib.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Structure.Monoidal.Internal.Product.

Require Import Enriched.Category.
Require Import Enriched.Functor.
Require Import Enriched.Natural.Transformation.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section SetEnrichedCategory.

Let V := InternalProduct_Monoidal (H:= Sets_Cartesian).
Definition SetEnrichedCategory := EnrichedCategory (V := V).

Program Definition FromOrdinaryCategory (C : Category) : SetEnrichedCategory := {|
  eobj     := obj[C];
  ehom     := fun x y => {| carrier:= x ~> y; is_setoid := homset x y|};
  eid      := fun x => {| morphism:= fun _ => id |};
  ecompose := fun x y z => {| morphism:= fun H => let (f, g) := H in (f ∘ g)%morphism |};
|}.

Program Definition FromOrdinaryFunctor {C D : Category} (F : (C ⟶ D)%functor_type) : FromOrdinaryCategory C ⟶ FromOrdinaryCategory D := {|
  efobj := fobj[F];
  efmap := fun x y => {| morphism:= fmap[F] |};
|}.
Next Obligation.
  symmetry.
  apply fmap_comp.
Qed.

Program Definition FromOrdinaryTransformation {C D : Category} {F G : (C ⟶ D)%functor_type} (a : (F ⟹ G)%transform_type) : FromOrdinaryFunctor F ⟹ FromOrdinaryFunctor G := {|
  etransform := fun c => {| morphism := fun _ => a c |};
|}.
Next Obligation.
  symmetry.
  apply naturality.
Qed.

End SetEnrichedCategory.