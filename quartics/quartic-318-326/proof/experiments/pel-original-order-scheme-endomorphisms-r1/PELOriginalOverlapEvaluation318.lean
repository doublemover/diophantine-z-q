module
public import PELOriginalChartIntersectionOpen318
public section
noncomputable section
namespace PELOriginalOverlapEvaluation318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalRatioEvaluationExt318 PELOriginalChartOverlapLocalization318
variable (τ : ℂ) (hτ : 0 < τ.im) (j k : Label 3)

/-- The actual overlap is nonzero and integral because its independently
constructed map into the original section field is genuinely injective.
This is not inferred for localization away from an arbitrary element. -/
instance overlapDomain : IsDomain (Overlap τ hτ j k) :=
  Function.Injective.isDomain (intoField τ hτ j k) (intoField_injective τ hτ j k)

/-- Every complex point of the actual principal intersection is ONE
original lift, with both original cubic chart denominators nonzero.
The two whole-ring evaluations agree, not only coordinate generators. -/
theorem original_evaluations (f : Overlap τ hτ j k →ₐ[ℂ] ℂ) :
    ∃ z : ComplexVectors, ∃ hj : value τ hτ 3 j z ≠ 0,
      ∃ hk : value τ hτ 3 k z ≠ 0,
        (∀ a : CoordinateChart τ hτ j,
          f (algebraMap _ (Overlap τ hτ j k) a) = algebraEvaluation τ hτ z j hj a) ∧
        f.comp (fromOther τ hτ j k) = algebraEvaluation τ hτ z k hk := by
  let fj := f.comp (IsScalarTower.toAlgHom ℂ (CoordinateChart τ hτ j) (Overlap τ hτ j k))
  obtain ⟨z,hj,hfj⟩ := PELOriginalFullCandidatePoints318.every_chart_point τ hτ j fj
  have hf (a : CoordinateChart τ hτ j) :
      f (algebraMap _ (Overlap τ hτ j k) a) = algebraEvaluation τ hτ z j hj a :=
    congrArg (fun g : CoordinateChart τ hτ j →ₐ[ℂ] ℂ => g a) hfj
  have hu : f (algebraMap _ (Overlap τ hτ j k) (ratioElement τ hτ j k)) ≠ 0 :=
    ((IsLocalization.Away.algebraMap_isUnit (ratioElement τ hτ j k)).map f).ne_zero
  have hk : value τ hτ 3 k z ≠ 0 := by
    rw [hf,actual_ratio_evaluation] at hu
    exact (div_ne_zero_iff.mp hu).1
  have hi : f (IsLocalization.Away.invSelf (ratioElement τ hτ j k)) =
      (f (algebraMap _ (Overlap τ hτ j k) (ratioElement τ hτ j k)))⁻¹ := by
    apply mul_left_cancel₀ hu
    rw [mul_inv_cancel₀ hu]
    simpa only [map_mul,map_one] using
      congrArg f (IsLocalization.Away.mul_invSelf (ratioElement τ hτ j k))
  refine ⟨z,hj,hk,hf,?_⟩
  apply AlgHom.toRingHom_injective
  apply ringHom_ext_ratios τ hτ k
  · intro c
    exact ((f.comp (fromOther τ hτ j k)).commutes c).trans
      ((algebraEvaluation τ hτ z k hk).commutes c).symm
  · intro i
    change f (fromOther τ hτ j k (ratioElement τ hτ k i)) = _
    rw [fromOther_ratio,chartRatios,map_mul,hi,hf,hf,
      actual_ratio_evaluation,actual_ratio_evaluation,actual_ratio_evaluation]
    field_simp [hj,hk]
end PELOriginalOverlapEvaluation318
