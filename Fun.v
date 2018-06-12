Set Warnings "-notation-overridden".

Require Import Category.Theory.
Require Import Category.Structure.Monoidal.
Require Import Category.Lib.

Require Import Enriched.Category.
Require Import Enriched.Functor.
Require Import Enriched.Natural.Transformation.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Fun.

Context {V0: Category} {V : Monoidal}.

Program Definition Fun (C D : EnrichedCategory) : Category := {|
  obj := C ⟶ D;
  hom := fun F G => F ⟹ G;
  homset := fun _ _ => enat_Setoid;
  id := fun F => enat_id;
  Category.compose := fun _ _ _ => VerticalComposite;
  compose_respects := fun _ _ _ => vert_comp_respects;
  id_left := fun _ _ _ => vert_comp_id_left;
  id_right := fun _ _ _ => vert_comp_id_right;
|}.
Next Obligation.
  intro.
  symmetry.
  apply vert_comp_assoc.
Qed.
Next Obligation.
  intro.
  apply vert_comp_assoc.
Qed.

End Fun.