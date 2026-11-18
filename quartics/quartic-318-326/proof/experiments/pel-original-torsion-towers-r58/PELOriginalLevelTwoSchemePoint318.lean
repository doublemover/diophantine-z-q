module
public import PELOriginalChartSchemePointIdentity318
public section
noncomputable section
namespace PELOriginalLevelTwoSchemePoint318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalAllLevelProjectiveMap318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
variable (τ : ℂ) (hτ : 0 < τ.im)

lemma base_nonzero (q : Base τ) : ∃ r : Label 2, baseVector τ hτ 0 q r ≠ 0 := by
  by_contra h
  push_neg at h
  exact baseVector_nonzero τ hτ 0 q (funext h)

lemma cover_nonzero (z : ComplexVectors) : ∃ r : Label 2, value τ hτ 2 r z ≠ 0 := by
  by_contra h
  push_neg at h
  exact coverVector_nonzero τ hτ 0 z (funext h)

/-- The actual level-two theta vector, with original gauge, as a genuine
Spec(C) point of projective THREE-space. No injectivity is asserted. -/
@[expose] def point (q : Base τ) :=
  ComplexProjectiveSchemePoint318.point (baseVector τ hτ 0 q) (base_nonzero τ hτ q)

@[reassoc] lemma over_complex (q : Base τ) :
    point τ hτ q ≫ ComplexProjectiveBase318.structureMap = 𝟙 _ :=
  ComplexProjectiveBase318.point_over _ _

lemma covering_point (z : ComplexVectors) :
    ComplexProjectiveSchemePoint318.point (fun r : Label 2 => value τ hτ 2 r z)
      (cover_nonzero τ hτ z) = point τ hτ (projection (P τ) z) := by
  apply ComplexProjectivePointEquality318.scheme_point_eq
  exact (original_covering_square τ hτ 0 z).symm
end PELOriginalLevelTwoSchemePoint318
