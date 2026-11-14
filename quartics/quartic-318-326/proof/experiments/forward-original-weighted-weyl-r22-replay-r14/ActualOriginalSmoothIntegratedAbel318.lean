module
public import ActualOriginalUnpairedMixedWeight318
public section
noncomputable section
namespace ActualOriginalSmoothIntegratedAbel318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCompactCircleCount318
open ActualOriginalJointPrefixControl318 ActualOriginalIntegratedMultiaxisAbel318
open ActualOriginalUnpairedMixedWeight318 MeasureTheory
open scoped ContDiff

/-- Actual smooth nonseparable W consumes the joint prefix integrals,
not pointwise products of five suprema. All mixed constants are produced.
The statement works for any measure and every original unit-direction
rectangle up to five axes. -/
theorem actual_smooth_integrated_abel (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ C : ℝ, 0≤C ∧ ∀ B R M : ℝ, 0<B → 0≤R → 0≤M →
      ∀ μ : Measure ℝ, ∀ as : List (TimeAxis (Coordinates ℤ)), as.length≤5 →
      (∀ a∈as, ‖integerEmbed a.step‖≤1 ∧ (a.steps : ℝ)≤R*B) →
      ∀ F : ℝ → ℂ, JointPrefixControl μ M as F → ∀ x,
        Integrable (fun t => F t*timeRectangle (latticeWeight B W) as x t) μ ∧
        (∫ t, ‖F t*timeRectangle (latticeWeight B W) as x t‖ ∂μ)≤C*(1+R)^as.length*M := by
  obtain ⟨C,hC,hb⟩ := actual_unpaired_five_order_control W hW hc
  refine ⟨C,hC,fun B R M hB hR hM μ as hlen ha F hF x => ?_⟩
  apply actual_integrated_multiaxis_abel μ (fun u => ‖integerEmbed u‖≤1) B⁻¹ R M
    (inv_nonneg.mpr (le_of_lt hB)) hR hM as (latticeWeight B W) C hC
  · intro a hamem
    refine ⟨(ha a hamem).1,?_⟩
    have hh := (div_le_iff₀ hB).mpr (ha a hamem).2
    simpa only [div_eq_mul_inv] using hh
  · intro us hu had z
    exact hb B hB us (hu.trans hlen) had z
  · exact hF

end ActualOriginalSmoothIntegratedAbel318
