module
public import AffineThreePoissonRows318
public import Mathlib.MeasureTheory.Integral.Prod
public section
noncomputable section
namespace ActualChartFourierFubini318
open MeasureTheory
open scoped FourierTransform
open AffineThreePoissonRows318

/-- Outer variable y, inner x. The expression matches the 1D iteration
exactly before reordering or multiplying the two circle factors. -/
@[expose] def weightedKernel (W : Cube) (ξ η z : ℝ) (p : ℝ×ℝ) : ℂ :=
  phase (-(p.1*η))*(phase (-(p.2*ξ))*W p.2 p.1 z)

theorem first_as_integral (W : Cube) (ξ y z : ℝ) :
    F₁ W ξ y z = ∫ x : ℝ,phase (-(x*ξ))*W x y z := by
  rw [F₁,Real.fourier_real_eq] <;> simp only [phase,Circle.smul_def,smul_eq_mul]

/-- The actual F₂ is the ordinary double integral of the SAME compact
chart with the product negative phase. Compact chart integrability of
weightedKernel is the explicit assumption, not an implicit integral default. -/
theorem second_as_product_integral (W : Cube) (ξ η z : ℝ)
    (h : Integrable (weightedKernel W ξ η z) ((volume : Measure ℝ).prod volume)) :
    F₂ W ξ η z =
      ∫ p : ℝ×ℝ,phase (-(p.2*ξ+p.1*η))*W p.2 p.1 z
        ∂((volume : Measure ℝ).prod volume) := by
  calc
    _ = ∫ y : ℝ,phase (-(y*η))*F₁ W ξ y z := by
      rw [F₂,Real.fourier_real_eq] <;> simp only [phase,Circle.smul_def,smul_eq_mul]
    _ = ∫ y : ℝ,∫ x : ℝ,weightedKernel W ξ η z (y,x) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [first_as_integral,←integral_const_mul] <;> rfl
    _ = ∫ p : ℝ×ℝ, weightedKernel W ξ η z p ∂((volume : Measure ℝ).prod volume) :=
      (integral_prod (weightedKernel W ξ η z) h).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [show -(p.2*ξ+p.1*η)=-(p.1*η)+-(p.2*ξ) by ring,phase_add]
      simp only [weightedKernel,mul_assoc]

end ActualChartFourierFubini318
