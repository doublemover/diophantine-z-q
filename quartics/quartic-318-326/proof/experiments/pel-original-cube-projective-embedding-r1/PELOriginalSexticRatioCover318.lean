module
public import PELOriginalSexticChartRatios318
public section
noncomputable section
namespace PELOriginalSexticRatioCover318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalSectionMultiplication318 PELOriginalWholeHZeroDimension318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalCandidatePointEquivalence318 PELOriginalCandidateAffineTopology318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalPowerSectionLift318
open PELOriginalSexticChartRatios318
variable (τ : ℂ) (hτ : 0 < τ.im)

lemma theta_lift (N : ℕ) [NeZero N] (r : Label N) (z : ComplexVectors) :
    lift τ hτ N (asSection τ hτ N (thetaVector τ hτ N r)) z = value τ hτ N r z := by
  let f : PELOriginalPowerSectionDescent318.OriginalAutomorphic τ hτ N :=
    ⟨value τ hτ N r,PELOriginalLevelPowerSections318.holomorphic τ hτ N r,
      PELOriginalLevelPowerSections318.original_automorphy τ hτ N r⟩
  exact PELOriginalPowerSectionDescent318.lift_descend τ hτ N f z

/-- The source function is the recovered ENTIRE representative of the
actual whole sextic section, divided by the original cubic squared. -/
@[expose] def coverRatio (j : Label 3) (s : homogeneous τ hτ 6) (z : ComplexVectors) : ℂ :=
  lift τ hτ 6 (asSection τ hτ 6 s) z / (value τ hτ 3 j z)^2

lemma baseRatio_projection (j : Label 3) (s : homogeneous τ hτ 6) (z : ComplexVectors) :
    baseRatio τ hτ j s (projection (P τ) z) = coverRatio τ hτ j s z := by
  rw [coverRatio,← theta_lift τ hτ 3 j z]
  let c := PELOriginalPolarizationAutomorphy318.factor τ hτ
    (PELOriginalAutomorphyRepresentatives318.shiftTo τ hτ
      ((core τ hτ).indexAt (projection (P τ) z)) z) z
  have hc : c ≠ 0 := PELOriginalPolarizationAutomorphy318.nonzero τ hτ _ _
  change s.val (projection (P τ) z) / ((thetaVector τ hτ 3 j).val (projection (P τ) z))^2 =
    ((c^6)⁻¹*s.val (projection (P τ) z)) /
      ((c^3)⁻¹*(thetaVector τ hτ 3 j).val (projection (P τ) z))^2
  rw [mul_pow,← inv_pow,← pow_mul]
  change _ = ((c^6)⁻¹*s.val (projection (P τ) z)) /
    ((c^6)⁻¹*((thetaVector τ hτ 3 j).val (projection (P τ) z))^2)
  exact (mul_div_mul_left _ _ (inv_ne_zero (pow_ne_zero 6 hc))).symm

/-- Every original representative evaluates to the SAME full candidate
function. In particular no source-point choice enters the output value. -/
theorem candidate_original (j : Label 3) (s : homogeneous τ hτ 6)
    (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    candidateRatio τ hτ j s ⟨ratioVector τ hτ 1 j z,
      PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨z,hz,rfl⟩⟩ =
        coverRatio τ hτ j s z := by
  rw [candidateRatio,sourcePoint_original,baseRatio_projection]

theorem theta_candidate_original (j : Label 3) (r : Label 6)
    (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    candidateRatio τ hτ j (thetaVector τ hτ 6 r) ⟨ratioVector τ hτ 1 j z,
      PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨z,hz,rfl⟩⟩ =
        value τ hτ 6 r z / (value τ hτ 3 j z)^2 := by
  rw [candidate_original,coverRatio,theta_lift]

/-- Holomorphy on the true original cubic chart, for EVERY full section. -/
theorem coverRatio_differentiable (j : Label 3) (s : homogeneous τ hτ 6) :
    DifferentiableOn ℂ (coverRatio τ hτ j s) {z | value τ hτ 3 j z ≠ 0} := by
  intro z hz
  exact ((PELOriginalPowerSectionLift318.entire τ hτ 6 (asSection τ hτ 6 s) z).div
    ((holomorphic τ hτ 3 j z).pow 2) (pow_ne_zero 2 hz)).differentiableWithinAt
end PELOriginalSexticRatioCover318
