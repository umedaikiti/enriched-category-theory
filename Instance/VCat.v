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
Require Import Enriched.Natural.Transformation.
Require Import Enriched.TwoCategory.
Require Import Enriched.Fun.
Require Import Enriched.Forget.Lib.


Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.


Section VCat.

Context {V0: Category} {V : Monoidal}.

Existing Instance enat_equiv_equivalence.

Let Cat_Monoidal := InternalProduct_Monoidal (H:= Cat_Cartesian).
Existing Instance Cat_Monoidal.

Program Definition eid_VCat (x : EnrichedCategory) : I ~{ Cat.Cat }~> Fun x x := {|
  fobj := fun _ => (EId : obj[Fun x x]);
  fmap := fun _ _ _ => enat_id;
|}.
Next Obligation.
  rewrite vert_comp_id_right.
  reflexivity.
Qed.

Program Definition ecompose_VCat (x y z : EnrichedCategory) : (Fun y z : obj[Cat.Cat]) ⨂ Fun x y ~{ Cat }~> Fun x z := {|
  fobj := fun FG => let (F, G) := FG in F ○ G;
  fmap := fun _ _ fg => let (f, g) := fg in _;
|}.
Next Obligation.
  apply (HorizontalComposite f g).
Defined.
Next Obligation.
  proper.
  simpl.
  unfold Lib.ecompose0.
  simpl in X, H.
  rewrite (H A).
  rewrite (X (e0 A)).
  reflexivity.
Qed.
Next Obligation.
  Existing Instance vert_comp_respects.
  unfold HorizontalComposite.
  rewrite outside_id, inside_id.
  intro.
  simpl.
  apply ecomp0_id_left.
Qed.
Next Obligation.
  apply interchange_law.
Qed.

Program Definition iso_functor_comp_id_left {C D : EnrichedCategory} {F : C ⟶ D} : (Id[D] ○ F : obj[Fun C D]) ≅ F := {|
  to := {| etransform := fun _ => eid; |};
  from := {| etransform := fun _ => eid; |};
|}.
Next Obligation.
  rewrite post_id, pre_id.
  normal.
  reflexivity.
Qed.
Next Obligation.
  rewrite post_id, pre_id.
  normal.
  reflexivity.
Qed.
Next Obligation.
  intro.
  simpl.
  apply ecomp0_id_left.
Qed.
Next Obligation.
  intro.
  simpl.
  apply ecomp0_id_left.
Qed.

Program Definition iso_functor_comp_id_right {C D : EnrichedCategory} {F : C ⟶ D} : (F ○ Id[C] : obj[Fun C D]) ≅ F := {|
  to := {| etransform := fun _ => eid; |};
  from := {| etransform := fun _ => eid; |};
|}.
Next Obligation.
  normal.
  rewrite post_id, pre_id.
  reflexivity.
Qed.
Next Obligation.
  normal.
  rewrite post_id, pre_id.
  reflexivity.
Qed.
Next Obligation.
  intro.
  simpl.
  apply ecomp0_id_left.
Qed.
Next Obligation.
  intro.
  simpl.
  apply ecomp0_id_left.
Qed.

Program Definition iso_functor_comp_assoc {A B C D : EnrichedCategory} {F : C ⟶ D} {G : B ⟶ C} {H : A ⟶ B} : ((F ○ G) ○ H : obj[Fun A D]) ≅ F ○ (G ○ H) := {|
  to := {| etransform := fun _ => eid; |};
  from := {| etransform := fun _ => eid; |};
|}.
Next Obligation.
  rewrite post_id, pre_id.
  normal.
  reflexivity.
Qed.
Next Obligation.
  rewrite post_id, pre_id.
  normal.
  reflexivity.
Qed.
Next Obligation.
  intro.
  simpl.
  apply ecomp0_id_left.
Qed.
Next Obligation.
  intro.
  simpl.
  apply ecomp0_id_left.
Qed.

Program Definition VCat : TwoCategory := {|
  eobj := EnrichedCategory (V := V);
  ehom := fun C D => Fun C D;
  eid := eid_VCat;
  ecompose := ecompose_VCat;
|}.
Next Obligation.
  exists (fun x0 : () ∧ (x ⟶ y) => @iso_functor_comp_id_left _ _ (snd x0) : (Id[y] ○ snd x0 : obj[Fun x y])≅ snd x0).
  intros.
  destruct x0 as [x0 F], y0 as [y0 G].
  simpl in f.
  destruct f as [f' f].
  intro.
  simpl.
  Existing Instance ecompose0_respects.
  do 2 rewrite ecomp0_id_left.
  rewrite ecomp0_id_right.
  normal.
  reflexivity.
Qed.
Next Obligation.
  exists (fun x0 : (x ⟶ y) ∧ () => @iso_functor_comp_id_right _ _ (fst x0) : (fst x0 ○ Id[x] : obj[Fun x y])≅ fst x0).
  intros.
  destruct x0 as [x0 F], y0 as [y0 G].
  simpl in f.
  destruct f as [f' f].
  intro.
  simpl.
  rewrite efmap_id.
  rewrite ecomp0_id_left, ecomp0_id_right.
  reflexivity.
Qed.
Next Obligation.
  unshelve eexists (fun FGH => _).
  + destruct FGH as [[F G] H].
    simpl.
    apply iso_functor_comp_assoc.
  + intros.
    destruct x0 as [[F0 F1] F2], y0 as [[G0 G1] G2].
    simpl in f.
    destruct f as [[f0 f1] f2].
    intro.
    simpl.
    rewrite ecomp0_id_left.
    rewrite ecomp0_id_right.
    rewrite ecomp0_assoc.
    f_equiv.
    transitivity (efmap0 (F:=F0) _ _ (ecompose0 (f1 (G2 A)) ((efmap (EnrichedFunctor:=F1)) ∘ f2 A)%morphism)).
    rewrite (efmap_comp0 _ _ _ (f1 (G2 A)) (efmap ∘ f2 A)%morphism).
    unfold efmap0.
    normal.
    reflexivity.
    unfold efmap0.
    reflexivity.
Qed.

End VCat.

(*
Section VCat0.

Context {V0: Category} {V : Monoidal}.

Program Definition VCat0 : Category := {|
  obj := EnrichedCategory (V := V);
  hom := fun C D => C ⟶ D;
  id := fun _ => EId;
  Category.compose := fun _ _ _ => ECompose;
|}.
Next Obligation.

End VCat0.
*)