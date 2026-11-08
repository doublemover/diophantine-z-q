module
public import AdmissibleAnalyticSections318
public import LiteralPlaneBiholomorph318
public section
noncomputable section
open scoped Manifold ContDiff
namespace NaturalPeriodPlaneComparison318
open ModularArithmeticCoordinates318 ThreeArithmeticQuotient318
open LiteralThreePlanePoints318 LiteralPlaneComparison318
set_option maxHeartbeats 400000

/-- The original period projection followed by the original literal-plane
comparison. This does not select a new period branch or change either atlas. -/
@[expose] def periodToPlane (N : ℕ) [NeZero N] (tau : Locus) : Plane :=
  comparison N (sourceProjection tau)

lemma periodToPlane_j (N : ℕ) [NeZero N] (tau : Locus) :
    planeJ (periodToPlane N tau) = ActualQJ318.jInvariant tau.val :=
  comparison_projection_j N tau

lemma periodToPlane_x (N : ℕ) [NeZero N] (tau : Locus) :
    planeX (periodToPlane N tau) = sourceX (sourceProjection tau) :=
  comparison_x N (sourceProjection tau)

/-- Analyticity in the independently natural period atlas and the actual
literal quartic's independently constructed graph j atlas. -/
theorem periodToPlane_analytic (N : ℕ) [NeZero N] :
    letI := AdmissiblePeriodProjection318.complexChartedSpace
    letI := LiteralPlaneJAtlas318.complexChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (periodToPlane N) := by
  letI := AdmissiblePeriodProjection318.complexChartedSpace
  letI := AdmissibleJComplexAtlas318.complexChartedSpace
  letI := LiteralPlaneJAtlas318.complexChartedSpace
  exact (LiteralPlaneBiholomorph318.comparison_analytic N).comp
    AdmissiblePeriodProjection318.sourceProjection_analytic

/-- The actual quotient-cover branch composed with the actual plane
biholomorphism; all domains come from partial-diffeomorphism composition. -/
@[expose] def localBiholomorph (N : ℕ) [NeZero N] (tau : Locus) :
    letI := AdmissiblePeriodProjection318.complexChartedSpace
    letI := LiteralPlaneJAtlas318.complexChartedSpace
    PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) Locus Plane ω := by
  letI := AdmissiblePeriodProjection318.complexChartedSpace
  letI := AdmissibleJComplexAtlas318.complexChartedSpace
  letI := LiteralPlaneJAtlas318.complexChartedSpace
  exact (AdmissibleAnalyticSections318.localBiholomorph tau).trans
    (LiteralPlaneBiholomorph318.biholomorph N).toPartialDiffeomorph

lemma localBiholomorph_apply (N : ℕ) [NeZero N] (tau sigma : Locus) :
    letI := AdmissiblePeriodProjection318.complexChartedSpace
    letI := LiteralPlaneJAtlas318.complexChartedSpace
    localBiholomorph N tau sigma = periodToPlane N sigma := by
  letI := AdmissiblePeriodProjection318.complexChartedSpace
  letI := LiteralPlaneJAtlas318.complexChartedSpace
  change comparison N ((AdmissibleAnalyticSections318.inverseSection tau).symm sigma) = _
  rw [AdmissibleAnalyticSections318.inverseSection_symm]
  rfl

/-- The inverse is precisely the old covering inverse after the old plane
comparison inverse, not an arbitrary lift of the same j coordinate. -/
lemma localBiholomorph_inverse_apply (N : ℕ) [NeZero N] (tau : Locus) (p : Plane) :
    letI := AdmissiblePeriodProjection318.complexChartedSpace
    letI := LiteralPlaneJAtlas318.complexChartedSpace
    (localBiholomorph N tau).symm p =
      AdmissibleAnalyticSections318.inverseSection tau ((comparison N).symm p) := rfl

/-- The original natural period-to-plane map is locally biholomorphic
throughout the admissible locus. No global injectivity is asserted. -/
theorem periodToPlane_localDiffeomorph (N : ℕ) [NeZero N] :
    letI := AdmissiblePeriodProjection318.complexChartedSpace
    letI := LiteralPlaneJAtlas318.complexChartedSpace
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω (periodToPlane N) := by
  letI := AdmissiblePeriodProjection318.complexChartedSpace
  letI := AdmissibleJComplexAtlas318.complexChartedSpace
  letI := LiteralPlaneJAtlas318.complexChartedSpace
  intro tau
  exact (AdmissibleAnalyticSections318.sourceProjection_localDiffeomorph tau).comp
    ((LiteralPlaneBiholomorph318.biholomorph N).isLocalDiffeomorph (sourceProjection tau))

end NaturalPeriodPlaneComparison318
