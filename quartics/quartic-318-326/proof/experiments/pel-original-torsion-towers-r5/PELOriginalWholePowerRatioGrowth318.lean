module
public import PELOriginalWholePowerCompactBound318
public import PELOriginalPolynomialGrowthRegular318
public section
noncomputable section
namespace PELOriginalWholePowerRatioGrowth318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalSectionMultiplication318 PELOriginalWholeHZeroDimension318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalWholePowerChartRatios318 PELOriginalWholePowerRatioCover318
open PELOriginalWholePowerCompactBound318 PELOriginalCandidatePointEquivalence318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalChartAnalyticEvaluation318
open PELOriginalRatioEvaluationExt318
variable (τ : ℂ) (hτ : 0 < τ.im) (m : ℕ)

/-- The compact weight divides by the SAME original cubic coefficient,
giving an honest polynomial bound in the entire affine coordinate vector. -/
theorem base_ratio_bound (s : homogeneous τ hτ (3*m)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : Label 3, ∀ q : Base τ,
      (thetaVector τ hτ 3 j).val q ≠ 0 →
      ‖baseRatio τ hτ m j s q‖ ≤ C*(∑ i : Label 3,
        ‖(thetaVector τ hτ 3 i).val q/(thetaVector τ hτ 3 j).val q‖)^m := by
  obtain ⟨C,hC,hbound⟩ := exists_bound τ hτ m s
  refine ⟨C,hC,?_⟩
  intro j q hj
  have hn : 0 < ‖(thetaVector τ hτ 3 j).val q‖^m := pow_pos (norm_pos_iff.mpr hj) m
  have h := div_le_div_of_nonneg_right (hbound q) hn.le
  simpa only [baseRatio,norm_div,norm_pow,←div_pow,←Finset.sum_div,mul_div_assoc,cubicSize] using h

theorem cover_ratio_bound (s : homogeneous τ hτ (3*m)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : Label 3, ∀ z : ComplexVectors,
      value τ hτ 3 j z ≠ 0 →
      ‖coverRatio τ hτ m j s z‖ ≤
        C*(∑ i : Label 3, ‖value τ hτ 3 i z/value τ hτ 3 j z‖)^m := by
  obtain ⟨C,hC,hbound⟩ := base_ratio_bound τ hτ m s
  refine ⟨C,hC,?_⟩
  intro j z hj
  have hbase : (thetaVector τ hτ 3 j).val (projection (P τ) z) ≠ 0 := by
    intro hz
    have h := PELOriginalSexticRatioCover318.theta_lift τ hτ 3 j z
    change _ * (thetaVector τ hτ 3 j).val (projection (P τ) z) = _ at h
    rw [hz,mul_zero] at h
    exact hj h.symm
  simpa only [baseRatio_projection,PELOriginalSexticRatioGrowth318.cubic_ratio_projection] using
    hbound j (projection (P τ) z) hbase

/-- Actual all-degree section data for the whole-chart regularity engine.
No polynomial expression, finite-generation or multiplication-surjectivity
assumption is supplied. -/
@[expose] def data (j : Label 3) (s : homogeneous τ hτ (3*m)) :
    PELOriginalPolynomialGrowthFunction318.Data τ hτ j where
  onCandidate := candidateRatio τ hτ m j s
  onCover := coverRatio τ hτ m j s
  continuous := candidateRatio_continuous τ hτ m j s
  differentiable z hz :=
    (PELOriginalPowerSectionLift318.entire τ hτ (3*m) (asSection τ hτ (3*m) s) z).div
      ((holomorphic τ hτ 3 j z).pow m) (pow_ne_zero m hz)
  original := candidate_original τ hτ m j s
  growth := by
    obtain ⟨C,hC,hb⟩ := cover_ratio_bound τ hτ m s
    refine ⟨C,hC,m,?_⟩
    intro f
    obtain ⟨z,hz,hf⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j f
    have hlocus : toLocus τ hτ j f =
        (⟨ratioVector τ hτ 1 j z,
          PELOriginalFullCandidatePoints318.original_subset_candidate τ hτ j ⟨z,hz,rfl⟩⟩ : Locus τ hτ j) := by
      apply Subtype.ext
      rw [hf]
      exact PELOriginalFullCandidatePoints318.pointVector_original τ hτ j z hz
    rw [hlocus,candidate_original]
    have he : ∑ i : Label 3, ‖f (ratioElement τ hτ j i)‖ =
        ∑ i : Label 3, ‖value τ hτ 3 i z/value τ hτ 3 j z‖ := by
      simp only [hf,actual_ratio_evaluation]
    rw [he]
    exact (hb j z hz).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => norm_nonneg _))
        (le_add_of_nonneg_left zero_le_one) m) hC)
end PELOriginalWholePowerRatioGrowth318
