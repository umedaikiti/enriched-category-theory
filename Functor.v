Set Warnings "-notation-overridden".

Require Import Category.Theory.
Require Import Category.Structure.Monoidal.
Require Import Category.Lib.

Require Import Enriched.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.


Section Functor.
Context {V0: Category} {V : Monoidal}.

Class EnrichedFunctor {C D : EnrichedCategory} := {
  efobj : C -> D;
  efmap {x y : C} : ehom x y ~> ehom (efobj x) (efobj y);

  efmap_id {x : C} : efmap ∘ eid << I ~~> ehom (efobj x) (efobj x) >> eid;
  efmap_comp {x y z : C} : ecompose ∘ bimap efmap efmap << ehom y z ⨂ ehom x y ~~> ehom (efobj x) (efobj z) >> efmap ∘ ecompose
}.

End Functor.

Coercion efobj : EnrichedFunctor >-> Funclass.

Bind Scope enriched_functor_scope with EnrichedFunctor.
Delimit Scope enriched_functor_type_scope with enriched_functor_type.
Delimit Scope enriched_functor_scope with enriched_functor.
Open Scope enriched_functor_type_scope.
Open Scope enriched_functor_scope.
Notation "C ⟶ D" := (@EnrichedFunctor _ _ C D)
  (at level 90, right associativity) : enriched_functor_type_scope.

Section Identity.
Context {V0: Category} {V : Monoidal}.

Program Definition EId {C : EnrichedCategory} : C ⟶ C := {|
  efobj := fun x => x;
  efmap := fun _ _ => id;
|}.
End Identity.

Notation "Id[ C ]" := (@EId _ _ C) (at level 9, format "Id[ C ]") : enriched_functor_scope.

Section Compose.
Context {V0: Category} {V : Monoidal}.

Program Definition ECompose
        {C : EnrichedCategory} {D : EnrichedCategory} {E : EnrichedCategory}
        (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E := {|
  efobj := fun x => efobj (efobj x);
  efmap := fun _ _ => (efmap ∘ efmap)%morphism;
|}.
Next Obligation.
  rewrite comp_assoc_sym.
  rewrite efmap_id.
  apply efmap_id.
Qed.
Next Obligation.
  rewrite bimap_comp.
  rewrite comp_assoc.
  rewrite efmap_comp.
  rewrite comp_assoc_sym.
  rewrite efmap_comp.
  apply comp_assoc.
Qed.
End Compose.

Notation "F ○ G" := (ECompose F G)
  (at level 40, left associativity) : enriched_category_scope.

(*
Section Setoid.
Context {V0: Category} {V : Monoidal}.

Program Instance EnrichedFunctor_Setoid {C D : EnrichedCategory} : Setoid (C ⟶ D) := {
  equiv := fun F G =>
    (* Equality of objects in a category is taken to be isomorphism *)
    { iso : ∀ x : C, F x ≅ G x
    & ∀ (x y : C) (f : x ~> y),
        fmap[F] f ≈ from (iso y) ∘ fmap[G] f ∘ to (iso x) }
}.
End Setoid.
*)
