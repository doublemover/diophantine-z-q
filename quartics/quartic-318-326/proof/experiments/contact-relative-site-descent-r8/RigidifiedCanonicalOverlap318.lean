module
public import RelativeCechClassEffectivity318
public section
noncomputable section
namespace RigidifiedCanonicalOverlap318
open AlgebraicGeometry CategoryTheory ActualOverlapDiagram318 ActualDescentBaseChangeDiagram318
open RelativeRigidifiedLine318 RigidifiedLineIsomorphism318 RigidifiedCechNerve318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
  (e : S ⟶ X) (e' : S' ⟶ X') (square : e' ≫ f = g ≫ e)

lemma common_pointed : doubleSection f g e e' square ≫ (first f ≫ f) =
    (first g ≫ g) ≫ e := by
  rw [← Category.assoc,double_first,Category.assoc,square,Category.assoc]

abbrev pulled (L : RigidifiedLine e) := RigidifiedPointedPullback318.line e e' f g square L

@[expose] def leftComparison (L : RigidifiedLine e) :=
  RigidifiedCanonicalComposition318.compositionAlong e e' (doubleSection f g e e' square)
    f (first f) g (first g) square (double_first f g e' e square)
    (first f ≫ f) (first g ≫ g) rfl rfl (common_pointed f g e e' square) L
@[expose] def rightComparison (L : RigidifiedLine e) :=
  RigidifiedCanonicalComposition318.compositionAlong e e' (doubleSection f g e e' square)
    f (second f) g (second g) square (double_second f g e' e square)
    (first f ≫ f) (first g ≫ g) (edge_condition f).symm (edge_condition g).symm
    (common_pointed f g e e' square) L

/-- The canonical original overlap is compatible with the actual pulled
rigidification, by the original canonical path comparisons at both faces. -/
@[expose] def overlap (L : RigidifiedLine e) :
    Overlap f g e e' square (pulled f g e e' square L) :=
  RigidifiedIsoCoherence318.compose _ (leftComparison f g e e' square L)
    (RigidifiedIsoCoherence318.inverse _ (rightComparison f g e e' square L))

lemma overlap_hom (L : RigidifiedLine e) :
    (overlap f g e e' square L).iso.hom = CanonicalSheafOverlap318.actual L.line.object f := by
  have h₀ := RigidifiedCanonicalComposition318.compositionAlong_hom
    e e' (doubleSection f g e e' square) f (first f) g (first g)
    square (double_first f g e' e square) (first f ≫ f) (first g ≫ g) rfl rfl
    (common_pointed f g e e' square) L
  have h₁ : (rightComparison f g e e' square L).iso =
      (PullbackPathComposition318.iso (second f) f (first f ≫ f) (edge_condition f).symm).app L.line.object :=
    Iso.ext (RigidifiedCanonicalComposition318.compositionAlong_hom
      e e' (doubleSection f g e e' square) f (second f) g (second g)
      square (double_second f g e' e square) (first f ≫ f) (first g ≫ g)
      (edge_condition f).symm (edge_condition g).symm (common_pointed f g e e' square) L)
  change (leftComparison f g e e' square L).iso.hom ≫
    (rightComparison f g e e' square L).iso.inv = _
  rw [h₁]
  change (leftComparison f g e e' square L).iso.hom ≫ _ = _
  rw [show (leftComparison f g e e' square L).iso.hom = _ from h₀] <;> rfl
end RigidifiedCanonicalOverlap318
