module
public import PELOriginalWholePowerChartRatios318
public import PELOriginalSexticRatioCover318
public section
noncomputable section
namespace PELOriginalWholePowerRatioCover318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalSectionMultiplication318 PELOriginalWholeHZeroDimension318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalCandidatePointEquivalence318 PELOriginalCandidateAffineTopology318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalPowerSectionLift318
open PELOriginalWholePowerChartRatios318
open PELOriginalSexticRatioCover318 (theta_lift)
variable (τ : ℂ) (hτ : 0 < τ.im) (m : ℕ)

/-- The source function is the recovered ENTIRE representative of the
actual whole degree3m section, divided by the original cubic to power m. -/
@[expose] def coverRatio (j : Label 3) (s : homogeneous τ hτ (3*m)) (z : ComplexVectors) : ℂ :=
  lift τ hτ (3*m) (asSection τ hτ (3*m) s) z / (value τ hτ 3 j z)^m

lemma baseRatio_projection (j : Label 3) (s : homogeneous τ hτ (3*m)) (z : ComplexVectors) :
    baseRatio τ hτ m j s (projection (P τ) z) = coverRatio τ hτ m j s z := by
  rw [coverRatio,← theta_lift τ hτ 3 j z]
  let c := PELOriginalPolarizationAutomorphy318.factor τ hτ
    (PELOriginalAutomorphyRepresentatives318.shiftTo τ hτ
      ((core τ hτ).indexAt (projection (P τ) z)) z) z
  have hc : c ≠ 0 := PELOriginalPolarizationAutomorphy318.nonzero τ hτ _ _
  change s.val (projection (P τ) z) / ((thetaVector τ hτ 3 j).val (projection (P τ) z))^m =
    ((c^(3*m))⁻¹*s.val (projection (P τ) z)) /
      ((c^3)⁻¹*(thetaVector τ hτ 3 j).val (projection (P τ) z))^m
  rw [mul_pow,← inv_pow,← pow_mul]
  change _ = ((c^(3*m))⁻¹*s.val (projection (P τ) z)) /
    ((c^(3*m))⁻¹*((thetaVector τ hτ 3 j).val (projection (P τ) z))^m)
  exact (mul_div_mul_left _ _ (inv_ne_zero (pow_ne_zero (3*m) hc))).symm

/-- Every original representative evaluates to the SAME full candidate
function. In particular no source-point choice enters the output value. -/
theorem candidate_original (j : Label 3) (s : homogeneous τ hτ (3*m))
    (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    candidateRatio τ hτ m j s ⟨ratioVector τ hτ 1 j z,
      PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨z,hz,rfl⟩⟩ =
        coverRatio τ hτ m j s z := by
  rw [candidateRatio,sourcePoint_original,baseRatio_projection]

theorem theta_candidate_original [NeZero (3*m)] (j : Label 3) (r : Label (3*m))
    (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    candidateRatio τ hτ m j (thetaVector τ hτ (3*m) r) ⟨ratioVector τ hτ 1 j z,
      PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨z,hz,rfl⟩⟩ =
        value τ hτ (3*m) r z / (value τ hτ 3 j z)^m := by
  rw [candidate_original,coverRatio,theta_lift]

/-- Holomorphy on the true original cubic chart, for EVERY full section. -/
theorem coverRatio_differentiable (j : Label 3) (s : homogeneous τ hτ (3*m)) :
    DifferentiableOn ℂ (coverRatio τ hτ m j s) {z | value τ hτ 3 j z ≠ 0} := by
  intro z hz
  exact ((PELOriginalPowerSectionLift318.entire τ hτ (3*m) (asSection τ hτ (3*m) s) z).div
    ((holomorphic τ hτ 3 j z).pow m) (pow_ne_zero m hz)).differentiableWithinAt
end PELOriginalWholePowerRatioCover318
