module
public import PELOriginalChartSchemePointIdentity318
public import PELOriginalChartOverlapLocalization318
public section
noncomputable section
namespace PELOriginalChartIntersectionOpen318
open AlgebraicGeometry CategoryTheory
open PELOriginalLevelTheta318 PELOriginalCandidateAffineCharts318
open PELOriginalCandidateNineChartCover318 PELOriginalChartAnalyticEvaluation318
open PELOriginalReducedProjectiveCandidate318
open HomogeneousQuotientChart318 HomogeneousQuotientChartSupport318
variable (τ : ℂ) (hτ : 0 < τ.im) (j k : Label 3)

/-- The preimage of the other actual candidate chart is the literal
principal open of the original cubic ratio. This equality holds on the
whole prime spectrum; it is not inferred from complex-point equality. -/
theorem preimage_chart :
    (chartMap τ hτ j) ⁻¹ᵁ candidateChart τ hτ k =
      PrimeSpectrum.basicOpen (ratioElement τ hτ j k) := by
  ext q
  have h := HomogeneousQuotientChartSupport318.positive_fraction_mem j
    (coordinateChartMap τ hτ j q) 1 (by norm_num)
    (MvPolynomial.X k) (MvPolynomial.isHomogeneous_X ℂ k)
  have he := congrArg (fun f => f q)
    (PELOriginalChartSchemePointIdentity318.chart_ambient τ hτ j)
  change (MvPolynomial.X k ∉ (inclusion τ hτ (chartMap τ hτ j q)).asHomogeneousIdeal) ↔
    ratioElement τ hτ j k ∉ q.asIdeal
  rw [he]
  exact not_congr h.symm

/-- Inverting the actual ratio gives the genuine full chart intersection
as an open subset, retaining every nonclosed scheme prime. -/
theorem principal_range :
    Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap (CoordinateChart τ hτ j)
        (PELOriginalChartOverlapLocalization318.Overlap τ hτ j k)))) =
      ((chartMap τ hτ j) ⁻¹ᵁ candidateChart τ hτ k : Set _) := by
  rw [preimage_chart]
  exact PrimeSpectrum.localization_away_comap_range _ _
end PELOriginalChartIntersectionOpen318
