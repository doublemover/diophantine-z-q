module
public import ActualOriginalCompleteTwoAxisWeyl318
public section
noncomputable section
namespace ActualOriginalSmoothCompleteTwoAxis318
open QuadricCRTAssembly318 ActualOriginalCompactCircleCount318 ActualOriginalScaledCircle318
open ActualOriginalCanonicalSupportBox318 ActualOriginalCanonicalOverlapLength318
open ActualOriginalSmoothOverlapPlane318 ActualOriginalCompleteTwoAxisWeyl318
open ActualOriginalScaledDisplacementBlockCount318 ActualOriginalCompleteFrequencyBudget318
open ActualOriginalRationalBlockReciprocalSum318
open scoped ContDiff BigOperators

/-- The complete five-variable smooth compact sum, with a support radius
and all analytic constants PRODUCED before scales and frequencies. The
six remaining outer multiplicities are visible in the two cubic factors. -/
theorem actual_smooth_complete_two_axis_bound (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ R A L D : ℝ, 1≤R ∧ 0≤A ∧ 0≤L ∧ 0≤D ∧
      ∀ B : ℝ, 1≤B → ∀ t : ℝ,
      ‖scaledCircleSum κ t B W‖^2≤
        (2*(⌈R*B⌉ : ℝ)+1)^3*(4*(⌈R*B⌉ : ℝ)+1)^3*
          smoothPlaneCost A L D (2*R+3)*
          (completeEvenKernel ⌈R*B⌉ (2*(⌈R*B⌉ : ℝ)+1) t)^2 := by
  obtain ⟨R,hR,hs⟩ := actual_compact_support_radius W hc
  obtain ⟨A,L,D,hA,hL,hD,hplane⟩ := actual_smooth_overlap_plane_bound κ W hW hc
  refine ⟨R,A,L,D,hR,hA,hL,hD,fun B hB t => ?_⟩
  have hB0 : 0<B := by linarith
  have hH := actual_scaled_radius_nonneg R B (by linarith) (by linarith)
  have hHr : (0 : ℝ)≤(⌈R*B⌉ : ℝ) := by exact_mod_cast hH
  have hsize : 2*(⌈R*B⌉ : ℝ)+1≤(2*R+3)*B := by
    have hh := Int.ceil_lt_add_one (R*B)
    nlinarith
  rw [actual_circle_eq_finite κ B W (centeredBox ⌈R*B⌉)
    (actual_scaled_support_box W R B hB0 hs)]
  apply actual_complete_two_axis_weyl κ ⌈R*B⌉ (latticeWeight B W) t
    (2*(⌈R*B⌉ : ℝ)+1) (smoothPlaneCost A L D (2*R+3)) hH (by positivity)
    (actual_smooth_plane_cost_nonneg A L D (2*R+3) hA hL hD (by linarith))
  exact fun h c d e => hplane B (2*R+3) hB0 (by linarith) ⌈R*B⌉ hH hsize h c d e t

/-- Rational block counting is now consumed by the ENTIRE actual sum,
not just one isolated line. Denominator existence/range selection and a
sufficient five-direction minor-arc saving remain open. -/
theorem actual_smooth_complete_two_axis_rational (κ : ℤ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ R A L D : ℝ, 1≤R ∧ 0≤A ∧ 0≤L ∧ 0≤D ∧
      ∀ B : ℝ, 1≤B → ∀ a q : ℤ, 0<q → IsCoprime q a → ∀ t : ℝ,
      |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2 →
      ‖scaledCircleSum κ t B W‖^2≤
        (2*(⌈R*B⌉ : ℝ)+1)^3*(4*(⌈R*B⌉ : ℝ)+1)^3*
          smoothPlaneCost A L D (2*R+3)*
          ((16*(⌈R*B⌉ : ℝ)/(q : ℝ)+2)*
            reciprocalBlockBudget (2*(⌈R*B⌉ : ℝ)+1) q)^2 := by
  obtain ⟨R,A,L,D,hR,hA,hL,hD,hall⟩ := actual_smooth_complete_two_axis_bound κ W hW hc
  refine ⟨R,A,L,D,hR,hA,hL,hD,fun B hB a q hq ha t ht => ?_⟩
  have hH := actual_scaled_radius_nonneg R B (by linarith) (by linarith)
  have hHr : (0 : ℝ)≤(⌈R*B⌉ : ℝ) := by exact_mod_cast hH
  have hN : (0 : ℝ)≤2*(⌈R*B⌉ : ℝ)+1 := by positivity
  have hS := actual_complete_even_kernel_nonneg ⌈R*B⌉ (2*(⌈R*B⌉ : ℝ)+1) t hN
  have hb := actual_scaled_even_displacement_budget a q ⌈R*B⌉ t
    (2*(⌈R*B⌉ : ℝ)+1) hq ha hH ht hN
  apply (hall B hB t).trans
  apply mul_le_mul_of_nonneg_left
  · simpa only [pow_two] using mul_le_mul hb hb hS (hS.trans hb)
  · exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (actual_smooth_plane_cost_nonneg A L D (2*R+3) hA hL hD (by linarith))

end ActualOriginalSmoothCompleteTwoAxis318
