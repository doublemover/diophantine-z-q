module
public import ComplexProjectivePointEquality318
public import AffineComplexProjectiveVector318
public import PELOriginalFullCandidateSchemePoints318
public import PELOriginalProperComplexCandidate318
public section
noncomputable section
namespace PELOriginalChartSchemePointIdentity318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalChartAnalyticEvaluation318 PELOriginalChartEvaluationRegularity318
open PELOriginalCandidateNineChartCover318 PELOriginalCandidateChartBase318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalProjectiveCandidatePoints318 PELOriginalAllLevelProjectiveMap318
open PELOriginalPolarizationTransitions318 HomogeneousQuotientChart318 HomogeneousQuotientChartSupport318
variable (τ : ℂ) (hτ : 0<τ.im)

lemma cover_nonzero (z : ComplexVectors) : ∃ i : Label 3, value τ hτ 3 i z≠0 := by
  by_contra h
  push_neg at h
  exact coverVector_nonzero τ hτ 1 z (funext h)

@[reassoc] lemma chart_ambient (j : Label 3) :
    chartMap τ hτ j≫inclusion τ hτ=
      coordinateChartMap τ hτ j≫chartMorphism j := by
  rw [chartMap,Category.assoc,←actual_chart_square,←Category.assoc,actualChartIso_over]

/-- The actual quotient-chart Spec map has the SAME full homogeneous
prime as the original theta vector. Every homogeneous degree is tested
through the literal fraction in the original affine chart. -/
theorem chart_underlying (j : Label 3) (z : ComplexVectors) (hz : value τ hτ 3 j z≠0)
    (x : Spec (CommRingCat.of ℂ)) :
    ((Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom)≫
      chartMap τ hτ j)≫inclusion τ hτ) x=
      ComplexProjectiveMarkerPoint318.point (coverVector τ hτ 1 z) (cover_nonzero τ hτ z) := by
  rw [Category.assoc,chart_ambient]
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  rw [ComplexProjectiveMarkerPoint318.homogeneous_mem_iff]
  change p ∈ (chartMorphism j (coordinateChartMap τ hτ j
    (Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom) x))).asHomogeneousIdeal ↔ _
  rw [←fraction_mem]
  have hx : x=(⟨⊥,inferInstance⟩ : PrimeSpectrum ℂ) := Subsingleton.elim _ _
  subst x
  change algebraEvaluation τ hτ z j hz
    ((quotientMap (PELOriginalCubicRelationIdeal318.relations τ hτ) j).rangeRestrict
      (fraction j n p hp))=0 ↔ _
  rw [fraction_formula,div_eq_zero_iff]
  exact or_iff_left (pow_ne_zero n hz)

/-- Literal scheme-morphism identity between the whole-chart evaluation
point and the original globally defined candidate point. -/
theorem chart_point (j : Label 3) (z : ComplexVectors) (hz : value τ hτ 3 j z≠0) :
    Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom)≫chartMap τ hτ j=
      candidateComplexPoint τ hτ (projection (P τ) z) := by
  apply (cancel_mono (inclusion τ hτ)).mp
  apply ext_of_apply_closedPoint_eq ComplexProjectiveBase318.structureMap
  · rw [Category.assoc]
    change (Spec.map (CommRingCat.ofHom (algebraEvaluation τ hτ z j hz).toRingHom)≫
      chartMap τ hτ j)≫PELOriginalProperComplexCandidate318.structureMap τ hτ=𝟙 _
    rw [Category.assoc,chart_over_complex_base]
    exact AffineComplexProjectiveVector318.point_over (algebraEvaluation τ hτ z j hz)
  · rw [Category.assoc]
    exact PELOriginalProperComplexCandidate318.candidate_point_over τ hτ _
  · rw [chart_underlying,candidateComplexPoint_inclusion,ambientPoint_underlying]
    apply ComplexProjectivePointEquality318.marker_of_projective
    exact (original_covering_square τ hτ 1 z).symm

/-- The genuine candidate Spec(C)-point map remains injective on the
original analytic torus. This consumes the proved original theta
embedding, not a transported scheme structure or assumed group law. -/
theorem candidate_point_injective : Function.Injective (candidateComplexPoint τ hτ) := by
  intro q r h
  have he := congrArg (fun p => (p≫inclusion τ hτ) (IsLocalRing.closedPoint ℂ)) h
  simp only [candidateComplexPoint_inclusion,ambientPoint_underlying] at he
  apply PELOriginalLevelThreePointSeparation318.injective τ hτ
  exact ComplexProjectivePointEquality318.projective_of_marker _ _ _ _ he
end PELOriginalChartSchemePointIdentity318
