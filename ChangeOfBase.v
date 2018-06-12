Set Warnings "-notation-overridden".

Require Import Category.Theory.
Require Import Category.Structure.Monoidal.
Require Import Category.Lib.
Require Import Category.Functor.Structure.Monoidal.

Require Import Enriched.Category.
Require Import Enriched.Functor.
Require Import Enriched.Natural.Transformation.
Require Import Enriched.Instance.VCat.
Require Import Enriched.Forget.Lib.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section ChangeOfBase.

Context {V0 V0' : Category}.
Context {V : @Monoidal V0}.
Context {V' : @Monoidal V0'}.

Program Definition change_of_base {F : (V0 ⟶ V0')%functor_type} {lax : @LaxMonoidalFunctor _ _ V V' F} (C : @EnrichedCategory _ V) : @EnrichedCategory _ V' := {|
  eobj := eobj;
  ehom := fun x y => F (ehom x y);
  eid := fun x => (fmap eid ∘ lax_pure)%morphism;
  ecompose := fun x y z => (fmap ecompose ∘ lax_ap)%morphism;
|}.
Next Obligation.
  transitivity (fmap[F] ecompose ∘ lax_ap[F] ∘ (fmap[F] eid  ⨂ fmap[F] id[ehom x y] ∘ lax_pure[_] ⨂ id[F (ehom x y)]))%morphism.
  rewrite <- bimap_comp.
  normal.
  reflexivity.
  rewrite comp_assoc.
  rewrite (comp_assoc_sym _ lax_ap).
  rewrite <- (naturality (f:=((eid : I ~> ehom y y, id[ehom x y]) : (I, ehom x y) ~{ V0 ∏ V0 }~> (ehom y y, ehom x y))) (Transform:=(ap_functor_nat (F:=F) (LaxMonoidalFunctor:=lax)))).
  simpl.
  normal.
  rewrite eid_left.
  symmetry.
  apply lax_monoidal_unit_left.
Qed.
Next Obligation.
  transitivity (fmap[F] ecompose ∘ lax_ap[F] ∘ (id[F (ehom x y)] ⨂ fmap[F] eid ∘ id[F (ehom x y)] ⨂ lax_pure[_]))%morphism.
  rewrite <- bimap_comp.
  normal.
  reflexivity.
  rewrite comp_assoc.
  rewrite (comp_assoc_sym _ lax_ap).
  assert (lax_ap[F] ∘ id[F (ehom x y)] ⨂ fmap[F] eid ≈ lax_ap[F] ∘ fmap[((⨂) ○ F ∏⟶ F)%category] ((id[ehom x y], eid) : (ehom x y, I) ~{ V0 ∏ V0 }~> (ehom x y, ehom x x)))%morphism.
  normal.
  compute.
  rewrite fmap_id.
  reflexivity.
  rewrite X.
  rewrite <- (naturality (f:=((id[ehom x y], (eid : I ~> ehom x x)) : (ehom x y, I) ~{ V0 ∏ V0 }~> (ehom x y, ehom x x))) (Transform:=(ap_functor_nat (F:=F) (LaxMonoidalFunctor:=lax)))).
  simpl.
  normal.
  rewrite eid_right.
  symmetry.
  apply lax_monoidal_unit_right.
Qed.
Next Obligation.
  transitivity (fmap[F] (ecompose (z:=w)) ∘ lax_ap[F] ∘ (fmap[F] (ecompose (y:=z)) ⨂ id[F (ehom x y)] ∘ lax_ap[F] ⨂ id[F (ehom x y)]))%morphism.
  rewrite <- bimap_comp.
  normal.
  reflexivity.
  transitivity (fmap[F] (ecompose (x:=x)) ∘ lax_ap[F] ∘ (id[F (ehom z w)] ⨂ fmap[F] (ecompose (y:=y)) ∘ id[F (ehom z w)] ⨂ lax_ap[F]) ∘ tensor_assoc)%morphism.
  Focus 2.
  rewrite <- bimap_comp.
  normal.
  reflexivity.
  do 2 rewrite comp_assoc.
  do 2 rewrite (comp_assoc_sym _ lax_ap).
  do 2 rewrite <- fmap_id.
  rewrite <- (naturality (f:=((ecompose (y:=z), id[ehom x y]) : (_, ehom x y) ~{ V0 ∏ V0 }~> (ehom y w, ehom x y))) (Transform:=(ap_functor_nat (F:=F) (LaxMonoidalFunctor:=lax)))).
  rewrite <- (naturality (f:=((id[ehom z w], ecompose (y:=y)) : (ehom z w, _) ~{ V0 ∏ V0 }~> (ehom z w, ehom x z))) (Transform:=(ap_functor_nat (F:=F) (LaxMonoidalFunctor:=lax)))).
  simpl.
  repeat rewrite comp_assoc.
  do 2 rewrite <- fmap_comp.
  rewrite ecomp_assoc.
  rewrite fmap_comp.
  repeat rewrite comp_assoc.
  rewrite (comp_assoc_sym _ _ (lax_ap[F] ⨂ fmap[F] id)).
  rewrite (comp_assoc_sym _ (fmap[F] tensor_assoc)).
  rewrite (comp_assoc (fmap[F] tensor_assoc)).
  rewrite fmap_id.
  rewrite lax_monoidal_assoc.
  normal.
  reflexivity.
Qed.

End ChangeOfBase.