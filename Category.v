Set Warnings "-notation-overridden".

Require Import Category.Theory.
Require Import Category.Structure.Monoidal.
Require Import Category.Lib.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section EnrichedCategory.
Context {V0: Category} {V : Monoidal}.

Class EnrichedCategory := {
  eobj : Type;

  ehom : eobj -> eobj -> obj[V0];

  eid {x} : I ~> ehom x x;
  ecompose {x y z} : (ehom y z) ⨂ (ehom x y) ~> ehom x z;

  eid_left  {x y} : ecompose ∘ bimap eid id << I ⨂ ehom x y ~~> ehom x y >> unit_left;
  eid_right {x y} : ecompose ∘ bimap id eid << ehom x y ⨂ I ~~> ehom x y >> unit_right;

  ecomp_assoc {x y z w} : ecompose ∘ bimap ecompose id << (ehom z w ⨂ ehom y z) ⨂ ehom x y ~~> ehom x w >> ecompose ∘ bimap id ecompose ∘ tensor_assoc
}.

End EnrichedCategory.

Bind Scope enriched_category_scope with Category.
Delimit Scope enriched_category_scope with enriched_category.

Coercion eobj : EnrichedCategory >-> Sortclass.
Open Scope enriched_category_scope.