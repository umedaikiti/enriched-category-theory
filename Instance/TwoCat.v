Set Warnings "-notation-overridden".

Require Import Category.Theory.
Require Import Category.Structure.Monoidal.
Require Import Category.Lib.

Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Natural.Transformation.

Require Import Enriched.Category.
Require Import Enriched.TwoCategory.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Cat.

Program Definition eid_2cat C : (1 ⟶ [C, C])%functor_type := {|
  fobj := fun _ => Id;
  fmap := fun _ _ _ => nat_id;
|}.

Definition horizontal_composition {C D E : Category} {F G : C ⟶ D} {H K : D ⟶ E} (f : F ⟹ G) (g : H ⟹ K) : H ○ F ⟹ K ○ G := nat_compose (inside f K) (outside g F).

Lemma horizontal_composition_respects {C D E : Category} {F G : C ⟶ D} {H K : D ⟶ E} : Proper (equiv (A := F ⟹ G) ==> equiv (A := H ⟹ K) ==> equiv) horizontal_composition.
Proof.
  proper.
  unfold horizontal_composition.
  specialize (X A).
  specialize (X0 (F A)).
  rewrite X, X0.
  reflexivity.
Qed.

Definition fobj_2cat {C D E : Category} : ([D, E]) ∏ ([C, D]) -> ([C, E]) := fun FG : ([D, E]) ∏ ([C, D]) => let (F, G) := FG in F ○ G.

Definition fmap_2cat {C D E : Category} (x y : ([D, E]) ∏ ([C, D])) (fg : x ~{ ([D, E]) ∏ ([C, D]) }~> y) : fobj_2cat x ~{ [C, E] }~> fobj_2cat y.
Proof.
  destruct x as [x0 x1], y as [y0 y1].
  simpl in fg.
  destruct fg as [f g].
  simpl.
  exact (horizontal_composition g f).
Defined.

Lemma fmap_comp_2cat {C D E : Category} : ∀ (x y z : ([D, E]) ∏ ([C, D])) (f : y ~{ ([D, E]) ∏ ([C, D]) }~> z)
 (g : x ~{ ([D, E]) ∏ ([C, D]) }~> y),
 fmap_2cat x z (f ∘ g)%morphism ≈ (fmap_2cat y z f ∘ fmap_2cat x y g)%morphism.
Proof.
  intros.
  destruct x as [x0 x1], y as [y0 y1], z as [z0 z1].
  destruct f as [f0 f1], g as [g0 g1].
  simpl in f0, f1, g0, g1.
  simpl.
  intro.
  normal.
  repeat rewrite naturality.
  rewrite fmap_comp.
  normal.
  reflexivity.
Qed.

Program Definition ecompose_2cat C D E : (([D, E]) ∏ ([C, D])) ⟶ ([C, E]) := {|
  fobj := fobj_2cat;
  fmap := fmap_2cat;
  fmap_respects := _;
  fmap_id := _;
  fmap_comp := fmap_comp_2cat
|}.
Next Obligation.
  proper.
  simpl in X, H.
  unfold fmap_2cat.
  apply (horizontal_composition_respects _ _ H _ _ X A).
Qed.

Obligation Tactic := idtac.
Program Definition TwoCat : TwoCategory :={|
  eobj     := Category;
  ehom     := fun C D => ([C, D] : obj[Cat]);
  eid      := (eid_2cat : ∀ x : Category, (@I _ Cat_Monoidal) ~{ Cat }~> ([x, x]));
  ecompose := ecompose_2cat;
|}.
Next Obligation.
  intros C D.
  simpl.
  unshelve eexists _.
  intros.
  destruct x as [x' F].
  unfold snd.
  clear x'.
  isomorphism.
  transform.
  simpl.
  apply nat_id.
  simpl;do 2 rewrite <- fmap_comp;normal;reflexivity.
  simpl;do 2 rewrite <- fmap_comp;normal;reflexivity.
  transform.
  simpl;apply nat_id.
  simpl;do 2 rewrite <- fmap_comp;normal;reflexivity.
  simpl;do 2 rewrite <- fmap_comp;normal;reflexivity.
  simpl;rewrite <- fmap_comp;normal;reflexivity.
  simpl;rewrite <- fmap_comp;normal;reflexivity.
  compute.
  intros.
  destruct x as [x' x], y as [y' y], f as [f' f].
  clear x' y' f'.
  repeat rewrite fmap_id.
  rewrite id_left.
  reflexivity.
Qed.
Next Obligation.
  intros C D.
  simpl.
  unshelve eexists _.
  intros.
  destruct x as [F x'].
  unfold fst.
  isomorphism.
  transform.
  simpl.
  apply nat_id.
  simpl;do 2 rewrite <- fmap_comp;normal;reflexivity.
  simpl;do 2 rewrite <- fmap_comp;normal;reflexivity.
  transform.
  simpl;apply nat_id.
  simpl;do 2 rewrite <- fmap_comp;normal;reflexivity.
  simpl;do 2 rewrite <- fmap_comp;normal;reflexivity.
  simpl;rewrite <- fmap_comp;normal;reflexivity.
  simpl;rewrite <- fmap_comp;normal;reflexivity.
  intros [x x'] [y y'] [f f'] A.
  compute.
  simpl in f.
  clear x' y' f'.
  repeat rewrite fmap_id.
  rewrite id_left, id_right.
  reflexivity.
Qed.
Next Obligation.
  intros A B C D.
  simpl.
  unshelve eexists _.
  intros [[x0 x1] x2].
  simpl.
  isomorphism.
  transform.
  intros;simpl;apply nat_id.
  simpl;normal;reflexivity.
  simpl;normal;reflexivity.
  transform.
  intros;simpl;apply nat_id.
  simpl;normal;reflexivity.
  simpl;normal;reflexivity.
  simpl;repeat rewrite fmap_id;normal;reflexivity.
  simpl;repeat rewrite fmap_id;normal;reflexivity.
  intros [[x0 x1] x2] [[y0 y1] y2].
  simpl.
  intros [[f0 f1] f2] A0.
  simpl.
  normal.
  rewrite fmap_id.
  normal.
  reflexivity.
Qed.
End Cat.
