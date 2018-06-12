Set Warnings "-notation-overridden".

Require Import Category.Theory.
Require Import Category.Structure.Monoidal.
Require Import Category.Lib.

Require Import Enriched.Category.
Require Import Enriched.Functor.
Require Import Enriched.Natural.Transformation.
Require Import Enriched.TwoCategory.
Require Import Enriched.Instance.VCat.
Require Import Enriched.Instance.TwoCat.
Require Import Enriched.Forget.Lib.
Require Import Enriched.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section ForgetfulFunctor.

Program Definition Forget_0cell {V0: Category} {V : Monoidal} (C : EnrichedCategory) : Category := {|
  obj := eobj;
  hom := ehom0;
  homset := fun x y => homset I (ehom x y);
  id := fun _ => eid;
  Category.compose := fun _ _ _ => ecompose0
|}.
Next Obligation.
  apply ecompose0_respects.
Qed.
Next Obligation.
  apply ecomp0_id_left.
Qed.
Next Obligation.
  apply ecomp0_id_right.
Qed.
Next Obligation.
  symmetry.
  apply ecomp0_assoc.
Qed.
Next Obligation.
  apply ecomp0_assoc.
Qed.

Program Definition Forget_1cell {V0: Category} {V : Monoidal} {C D : EnrichedCategory} (F : C ⟶ D) : ((Forget_0cell C) ⟶ (Forget_0cell D))%functor_type := {|
  fobj := fun X => F X;
  fmap := fun _ _ f => efmap0 _ _ f;
|}.
Next Obligation.
  proper.
  unfold efmap0.
  rewrite X.
  reflexivity.
Qed.
Next Obligation.
  apply efmap_id0.
Qed.
Next Obligation.
  apply efmap_comp0.
Qed.

Program Definition Forget_2cell {V0: Category} {V : Monoidal} {C D : EnrichedCategory} {F G : C ⟶ D} (f : F ⟹ G) : (Forget_1cell F ⟹ Forget_1cell G)%transform_type := {|
  transform := f;
|}.
Next Obligation.
  rewrite ecompose0_precompose.
  rewrite ecompose0_postcompose.
  unfold efmap0.
  normal.
  rewrite enaturality.
  reflexivity.
Qed.
Next Obligation.
  symmetry.
  apply Forget_2cell_obligation_1.
Qed.

Program Definition Forget_efmap {V0: Category} {V : Monoidal} {C D : EnrichedCategory} : (Fun C D ⟶ @Fun.Fun (Forget_0cell C) (Forget_0cell D))%functor_type := {|
  fobj := Forget_1cell;
  fmap := fun _ _ => Forget_2cell;
|}.
Next Obligation.
  symmetry.
  apply efmap_id0.
Qed.

Program Definition Forget {V0: Category} {V : Monoidal} : TwoFunctor VCat TwoCat := {|
  efobj := Forget_0cell;
  efmap := fun _ _ => Forget_efmap;
|}.
Next Obligation.
  unfold Forget_1cell.
  unfold efmap0.
  simpl.
  unshelve eexists (fun _ => _).
  {
    isomorphism.
    + transform.
      - intro.
        simpl.
        apply eid.
      - simpl.
        rewrite ecomp0_id_left.
        rewrite ecomp0_id_right.
        normal.
        reflexivity.
      - rewrite ecomp0_id_left.
        rewrite ecomp0_id_right.
        normal.
        reflexivity.
    + transform.
      - intro.
        simpl.
        apply eid.
      - simpl.
        rewrite ecomp0_id_left.
        rewrite ecomp0_id_right.
        normal.
        reflexivity.
      - rewrite ecomp0_id_left.
        rewrite ecomp0_id_right.
        normal.
        reflexivity.
    + simpl.
      apply ecomp0_id_left.
    + simpl.
      normal.
      apply ecomp0_id_left.
  }
  intros.
  simpl.
  do 2 rewrite ecomp0_id_right.
  reflexivity.
Qed.
Next Obligation.
  unshelve eexists (fun _ => _).
  {
  isomorphism.
  + destruct y0 as [F G].
    simpl.
    transform.
    - intro.
      simpl.
      apply eid.
    - simpl.
      rewrite ecomp0_id_right.
      rewrite ecomp0_id_left.
      unfold efmap0.
      simpl.
      normal.
      reflexivity.
    - simpl.
      rewrite ecomp0_id_right.
      rewrite ecomp0_id_left.
      unfold efmap0.
      simpl.
      normal.
      reflexivity.
  + destruct y0 as [F G].
    simpl.
    transform.
    - intro.
      simpl.
      apply eid.
    - simpl.
      rewrite ecomp0_id_right.
      rewrite ecomp0_id_left.
      unfold efmap0.
      simpl.
      normal.
      reflexivity.
    - simpl.
      rewrite ecomp0_id_right.
      rewrite ecomp0_id_left.
      unfold efmap0.
      simpl.
      normal.
      reflexivity.
  + destruct y0 as [F G].
    simpl.
    rewrite ecomp0_id_right.
    unfold efmap0.
    symmetry.
    rewrite efmap_id.
    reflexivity.
  + destruct y0 as [F G].
    simpl.
    rewrite ecomp0_id_right.
    unfold efmap0.
    do 2 rewrite efmap_id.
    reflexivity.
  }
  intros [F0 F1] [G0 G1].
  simpl.
  intros [f g] A.
  simpl.
  rewrite ecomp0_id_right.
  rewrite ecomp0_id_left.
  unfold efmap0.
  rewrite ecompose0_precompose.
  rewrite ecompose0_postcompose.
  normal.
  rewrite enaturality.
  reflexivity.
Qed.

End ForgetfulFunctor.
