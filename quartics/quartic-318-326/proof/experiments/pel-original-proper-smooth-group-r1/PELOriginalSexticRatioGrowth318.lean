module
public import PELOriginalSexticCompactBound318
public section
noncomputable section
namespace PELOriginalSexticRatioGrowth318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalSectionMultiplication318 PELOriginalWholeHZeroDimension318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalSexticChartRatios318 PELOriginalSexticRatioCover318
open PELOriginalSexticCompactBound318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Dividing the actual compact-section estimate by the SAME cubic
coefficient squared gives a quadratic bound in all actual chart ratios. -/
theorem base_ratio_bound (s : homogeneous τ hτ 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : Label 3, ∀ q : Base τ,
      (thetaVector τ hτ 3 j).val q ≠ 0 →
      ‖baseRatio τ hτ j s q‖ ≤
        C * ∑ i : Label 3, ‖(thetaVector τ hτ 3 i).val q /
          (thetaVector τ hτ 3 j).val q‖^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_bound τ hτ s
  refine ⟨C,hC,?_⟩
  intro j q hj
  have hn : 0 < ‖(thetaVector τ hτ 3 j).val q‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hj)
  have h := div_le_div_of_nonneg_right (hbound q) hn.le
  simpa only [baseRatio,norm_div,norm_pow,div_pow,Finset.sum_div,mul_div_assoc,cubicSize] using h

lemma cubic_ratio_projection (i j : Label 3) (z : ComplexVectors) :
    (thetaVector τ hτ 3 i).val (projection (P τ) z) /
      (thetaVector τ hτ 3 j).val (projection (P τ) z) =
        value τ hτ 3 i z / value τ hτ 3 j z := by
  rw [←theta_lift τ hτ 3 i z,←theta_lift τ hτ 3 j z]
  let c := PELOriginalPolarizationAutomorphy318.factor τ hτ
    (PELOriginalAutomorphyRepresentatives318.shiftTo τ hτ
      ((core τ hτ).indexAt (projection (P τ) z)) z) z
  have hc : c ≠ 0 := PELOriginalPolarizationAutomorphy318.nonzero τ hτ _ _
  change _ = ((c^3)⁻¹*(thetaVector τ hτ 3 i).val (projection (P τ) z)) /
    ((c^3)⁻¹*(thetaVector τ hτ 3 j).val (projection (P τ) z))
  exact (mul_div_mul_left _ _ (inv_ne_zero (pow_ne_zero 3 hc))).symm

/-- A single constant works for ALL original affine charts and EVERY
covering representative, including all former primitive-open boundaries. -/
theorem cover_ratio_bound (s : homogeneous τ hτ 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : Label 3, ∀ z : ComplexVectors,
      value τ hτ 3 j z ≠ 0 →
      ‖coverRatio τ hτ j s z‖ ≤
        C * ∑ i : Label 3, ‖value τ hτ 3 i z / value τ hτ 3 j z‖^2 := by
  obtain ⟨C,hC,hbound⟩ := base_ratio_bound τ hτ s
  refine ⟨C,hC,?_⟩
  intro j z hj
  have hbase : (thetaVector τ hτ 3 j).val (projection (P τ) z) ≠ 0 := by
    intro hz
    have h := theta_lift τ hτ 3 j z
    change _ * (thetaVector τ hτ 3 j).val (projection (P τ) z) = _ at h
    rw [hz,mul_zero] at h
    exact hj h.symm
  simpa only [baseRatio_projection,cubic_ratio_projection] using
    hbound j (projection (P τ) z) hbase
end PELOriginalSexticRatioGrowth318
