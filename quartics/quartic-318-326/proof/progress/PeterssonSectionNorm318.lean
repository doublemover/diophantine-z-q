module
public import SectionCoefficientBounds318
public section
noncomputable section
open SourceMetricCharts318 SectionCoefficientBounds318
namespace PeterssonSectionNorm318
set_option maxHeartbeats 0

/-- Quadratic-differential coordinate norm when the cotangent basis norm is
2/sqrt(h). The geometric Petersson/frame identification is explicit downstream. -/
@[expose] def quadraticNorm (h:ℝ) (q:ℂ) : ℝ := ‖q‖*(2/Real.sqrt h)^2

theorem quadraticNorm_formula (h:ℝ) (hh:0<h) (q:ℂ) :
    quadraticNorm h q=4*‖q‖/h := by
  rw [quadraticNorm,div_pow,Real.sq_sqrt hh.le]
  ring

theorem quadraticNorm_mul (h:ℝ) (a q:ℂ) :
    quadraticNorm h (a*q)=‖a‖*quadraticNorm h q := by
  rw [quadraticNorm,quadraticNorm,norm_mul]
  ring

theorem comparison_norm_bound (c:Chart) (h C:ℝ) (hh:0<h)
    (hcomp:c.coefficient (0,0)≤C*h) :
    quadraticNorm h (Chart.section0 c)≤4*C ∧
    quadraticNorm h (Chart.section1 c)≤4*C := by
  have hb:=Chart.coefficient_bounds c
  rw [quadraticNorm_formula h hh,quadraticNorm_formula h hh]
  constructor
  · apply (div_le_iff₀ hh).mpr
    linarith
  · apply (div_le_iff₀ hh).mpr
    linarith

theorem scaled_norm_bound (c:Chart) (h:ℝ) (hh:0<h)
    (hcomp:c.coefficient (0,0)≤12540153541944538512*h) :
    quadraticNorm h ((2765952000:ℂ)^2*Chart.section0 c)≤
      (2765952000:ℝ)^2*(4*12540153541944538512) ∧
    quadraticNorm h ((2765952000:ℂ)^2*Chart.section1 c)≤
      (2765952000:ℝ)^2*(4*12540153541944538512) := by
  have hb:=comparison_norm_bound c h 12540153541944538512 hh hcomp
  simp only [quadraticNorm_mul,norm_pow,Complex.norm_ofNat]
  constructor
  · exact mul_le_mul_of_nonneg_left hb.1 (by positivity)
  · exact mul_le_mul_of_nonneg_left hb.2 (by positivity)

end PeterssonSectionNorm318
#print axioms PeterssonSectionNorm318.scaled_norm_bound
