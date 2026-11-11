module
public import AffineComplexProjectiveVector318
public import ReducedComplexPointMorphisms318
public section
noncomputable section
namespace AffineProjectiveScaledVector318
open AlgebraicGeometry CategoryTheory
variable {ι A : Type*} [Finite ι] [CommRing A] [Algebra ℂ A]
  [Algebra.FiniteType ℂ A] [_root_.IsReduced A]
local instance standardGrading : GradedAlgebra
    (ComplexProjectiveMarkerPoint318.grading (ι := ι)) := MvPolynomial.gradedAlgebra
local instance structureFinite : LocallyOfFiniteType
    (AffineComplexProjectiveVector318.structureMap (A := A)) := by
  dsimp [AffineComplexProjectiveVector318.structureMap]
  infer_instance

/-- Equality of genuine projective scheme morphisms for two actual
unit-ideal vectors differing by a literal common regular scalar. Both
unit ideals are explicit; no nonzero coordinate is discarded. -/
theorem morphism_eq (u v : ι → A)
    (hu : Ideal.span (Set.range u)=⊤) (hv : Ideal.span (Set.range v)=⊤)
    (c : A) (hc : ∀ i,v i=u i*c) :
    AffineComplexProjectiveVector318.morphism v hv =
      AffineComplexProjectiveVector318.morphism u hu := by
  apply ReducedComplexPointMorphisms318.ext
    (AffineComplexProjectiveVector318.structureMap (A := A))
    ComplexProjectiveBase318.structureMap _ _
    (AffineComplexProjectiveVector318.over_complex _ _)
    (AffineComplexProjectiveVector318.over_complex _ _)
  intro p hp
  obtain ⟨f,rfl⟩ := AffineComplexProjectiveVector318.exists_algebraPoint p hp
  rw [AffineComplexProjectiveVector318.point_action,AffineComplexProjectiveVector318.point_action]
  apply ComplexProjectivePointEquality318.scheme_point_eq
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨f c,?_⟩
  funext i
  change f c*f (u i)=f (v i)
  rw [hc,map_mul,mul_comm]
end AffineProjectiveScaledVector318
