module
public import PELOriginalSexticChartMorphism318
public import PELOriginalChartSchemePointIdentity318
public section
noncomputable section
namespace PELOriginalSexticSchemePoint318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalPolarizationTransitions318 PELOriginalAllLevelProjectiveMap318
open PELOriginalLevelTheta318 PELOriginalChartAnalyticEvaluation318
variable (τ : ℂ) (hτ : 0<τ.im)

lemma base_nonzero (q : Base τ) : ∃ r : Label 6, baseVector τ hτ 4 q r≠0 := by
  by_contra h
  push_neg at h
  exact baseVector_nonzero τ hτ 4 q (funext h)

/-- The literal original level-six vector as a genuine over-C point of
projective scheme space, with the SAME selected original gauge. -/
@[expose] def point (q : Base τ) :=
  ComplexProjectiveSchemePoint318.point (baseVector τ hτ 4 q) (base_nonzero τ hτ q)

@[reassoc] lemma over_complex (q : Base τ) :
    point τ hτ q≫ComplexProjectiveBase318.structureMap=𝟙 _ :=
  ComplexProjectiveBase318.point_over _ _

/-- The regular chart morphism agrees with the global original sextic
point, independently of the cubic trivialization used to construct it. -/
theorem chart_action (j : Label 3) (z : ComplexVectors) (hz : value τ hτ 3 j z≠0) :
    Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom)≫
      PELOriginalSexticChartMorphism318.morphism τ hτ j=point τ hτ (projection (P τ) z) := by
  rw [PELOriginalSexticChartMorphism318.original_point_action]
  apply ComplexProjectivePointEquality318.scheme_point_eq
  trans coveringMap τ hτ 4 z
  · apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    refine ⟨((value τ hτ 3 j z)^2)⁻¹,?_⟩
    funext r
    change ((value τ hτ 3 j z)^2)⁻¹*value τ hτ 6 r z=
      value τ hτ 6 r z/(value τ hτ 3 j z)^2
    rw [div_eq_mul_inv,mul_comm]
  · exact (original_covering_square τ hτ 4 z).symm
end PELOriginalSexticSchemePoint318
