Set Warnings "-notation-overridden".

Require Import Category.Theory.
Require Import Category.Structure.Monoidal.
Require Import Category.Lib.
Require Import Category.Structure.Monoidal.Proofs.

Require Import Enriched.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.


Section One.
Context {V0: Category} {V : Monoidal}.

Program Definition E1 : EnrichedCategory := {|
  eobj     := Datatypes.unit;
  ehom     := fun _ _ => I;
  eid      := fun _ => id;
  ecompose := fun _ _ _ => unit_left
|}.
Next Obligation.
  normal.
  apply unit_identity.
Qed.
Next Obligation.
  rewrite id_unit_left.
  rewrite triangle_identity_left.
  apply comp_assoc.
Qed.
End One.

Notation "1" := E1 : enriched_category_scope.