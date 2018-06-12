Set Warnings "-notation-overridden".

Require Import Category.Theory.
Require Import Category.Structure.Monoidal.
Require Import Category.Lib.

Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.One.

Require Import Enriched.Category.
Require Import Enriched.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Def.

Definition Cat_Monoidal := InternalProduct_Monoidal (H:= Cat_Cartesian).

Definition TwoCategory := EnrichedCategory (V := Cat_Monoidal).
Definition TwoFunctor := @EnrichedFunctor _ Cat_Monoidal.

(*
Section Cell.
Context {C : TwoCategory}.
Definition zero_cell := @eobj _ Cat_Monoidal C.
Definition one_cell (x y : zero_cell) := obj[@ehom _ Cat_Monoidal C x y].
Definition two_cell {x y : zero_cell} (f g : one_cell x y) := @hom (@ehom _ Cat_Monoidal C x y) f g.

Definition id1 := fun x => @eid _ Cat_Monoidal C x () : one_cell x x.

Definition id2 := fun {x y : zero_cell} (f : one_cell x y)  => @id (@ehom _ Cat_Monoidal C x y) f : two_cell f f.

Definition comp1 := fun {x y z} (f : one_cell y z) (g : one_cell x y) => fobj[@ecompose _ Cat_Monoidal C x y z] (f, g).

Definition vert_comp := fun {x y} {f g h : one_cell x y} (a : two_cell g h) (b : two_cell f g) => @Category.compose (@ehom _ Cat_Monoidal C x y) f g h a b : two_cell f h.

Definition hori_comp := fun {x y z : zero_cell} {f g : one_cell y z} {h k : one_cell x y} (a : two_cell f g) (b : two_cell h k) => (@fmap _ _ (@ecompose _ Cat_Monoidal C x y z) (f, h) (g, k) (a, b) : two_cell (comp1 f h) (comp1 g k)).

Lemma id1_left x y (f : one_cell x y) : comp1 (id1 y) f ≈ f.
Abort.

End Cell.
*)

End Def.


