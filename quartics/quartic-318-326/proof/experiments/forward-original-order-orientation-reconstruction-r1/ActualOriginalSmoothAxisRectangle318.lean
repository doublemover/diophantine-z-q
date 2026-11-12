module
public import ActualOriginalMultiaxisAbel318
public section
noncomputable section
namespace ActualOriginalSmoothAxisRectangle318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalAxisRectangle318 ActualOriginalMultiaxisAbel318
open ActualOriginalFiniteAbel318 ActualOriginalScaledPairedMixedDifference318
open ActualOriginalFiveOrderWeightControl318
open scoped ContDiff

/-- The all-order increment producer is now consumed by an ACTUAL
multiaxis weighted rectangle. One C precedes scales, shifts, rectangles
and phases; no mixed variation budget is left as an external premise. -/
theorem actual_smooth_axis_rectangle (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ C : ℝ, 0≤C ∧ ∀ B R : ℝ, 0<B → 0≤R → ∀ h : Coordinates ℤ,
      ∀ as : List (Axis (Coordinates ℤ)), as.length≤5 →
      (∀ a∈as, 0≤a.cap ∧ ‖integerEmbed a.step‖≤1 ∧ (a.steps : ℝ)≤R*B ∧
        ∀ n≤a.steps+1, ‖prefix a.phase n‖≤a.cap) →
      ∀ x, ‖axisRectangle (latticePairedWeight B W h) as x‖≤
        C*(1+R)^as.length*axisCapProduct as := by
  obtain ⟨C,hC,hb⟩ := actual_unit_direction_five_order_weight_control W hW hc
  refine ⟨C,hC,fun B R hB hR h as hlen ha x => ?_⟩
  apply actual_multiaxis_abel (fun u => ‖integerEmbed u‖≤1) B⁻¹ R
    (inv_nonneg.mpr (le_of_lt hB)) hR as (latticePairedWeight B W h) C hC
  · intro a hamem
    obtain ⟨hcap,hu,hsize,hprefix⟩ := ha a hamem
    refine ⟨hcap,hu,?_,hprefix⟩
    have hh := (div_le_iff₀ hB).mpr hsize
    simpa only [div_eq_mul_inv] using hh
  · intro us hu had y
    have hh := hb B hB h us (hu.trans hlen) had y
    simpa only [div_eq_mul_inv,inv_pow] using hh

end ActualOriginalSmoothAxisRectangle318
