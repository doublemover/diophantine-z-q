module
public import PELOriginalPulledPeriodMetric318
public import PELOriginalPoincareIndependence318
public section
noncomputable section
namespace PELOriginalChartPeriodMetric318
open QuaternionicJointPeriodTopology318 PELJointComplexAtlas318
open PELUnlevelledComplexBase318 PELEffectiveNormOneAction318
open PELOriginalChartUniformizer318 PELOriginalSiegelMatrix318
open PELOriginalPulledPeriodMetric318 MobiusPoincarePullback318 PeterssonSectionNorm318
open scoped Topology Manifold ContDiff
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold
variable (e : OpenPartialHomeomorph UnlevelledBase ℂ) (p : UnlevelledBase)
  (hp : p∈e.source) (he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase)
  (τ : HalfPlane) (hτ : projection τ=p)

/-- The actual original period matrix in the produced SAME original chart
uniformizer, retaining its true covering projection and integral-period basis. -/
@[expose] def period (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := omega (uniformizer e p τ z)
include hp he hτ in
lemma determinant_density :
    ‖(deriv (period e p τ) 0).det‖=
      density (uniformizer e p τ) 0*(imaginary (τ:ℂ)).det := by
  have hu : 0<(uniformizer e p τ 0).im := by
    rw [uniformizer_zero e p hp τ hτ];exact τ.property
  simpa only [period,uniformizer_zero e p hp τ hτ] using
    PELOriginalPulledPeriodMetric318.determinant_density (uniformizer e p τ) 0
      (uniformizer_analytic e p hp he τ hτ).differentiableAt hu
include hp he hτ in
lemma determinant_petersson :
    quadraticNorm (density (uniformizer e p τ) 0) ((deriv (period e p τ) 0).det)=
      4*(imaginary (τ:ℂ)).det := by
  have hu : 0<(uniformizer e p τ 0).im := by
    rw [uniformizer_zero e p hp τ hτ];exact τ.property
  simpa only [period,uniformizer_zero e p hp τ hτ] using
    PELOriginalPulledPeriodMetric318.determinant_petersson (uniformizer e p τ) 0
      (uniformizer_analytic e p hp he τ hτ).differentiableAt hu
      (uniformizer_noncritical e p hp he τ hτ)

include hp he hτ in
/-- The metric ratio obtained from the genuine derivative is independent of
which representative of this SAME original base point is used. -/
lemma normalized_ratio_independent (σ : HalfPlane) (hσ : projection σ=p) :
    ‖(deriv (period e p τ) 0).det‖/(imaginary (τ:ℂ)).det=
      ‖(deriv (period e p σ) 0).det‖/(imaginary (σ:ℂ)).det := by
  have ht : (imaginary (τ:ℂ)).det≠0 := by
    rw [PELOriginalPeriodMetricDeterminant318.imaginary_determinant _ τ.property]
    exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 τ.property.ne'))
      (Complex.normSq_pos.mpr (PELOriginalSiegelNormalization318.parameter_ne _ τ.property)).ne'
  have hs : (imaginary (σ:ℂ)).det≠0 := by
    rw [PELOriginalPeriodMetricDeterminant318.imaginary_determinant _ σ.property]
    exact div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 σ.property.ne'))
      (Complex.normSq_pos.mpr (PELOriginalSiegelNormalization318.parameter_ne _ σ.property)).ne'
  rw [determinant_density e p hp he τ hτ,determinant_density e p hp he σ hσ,
    mul_div_cancel_right₀ _ ht,mul_div_cancel_right₀ _ hs]
  exact PELOriginalPoincareIndependence318.representative_independent e p hp he τ σ hτ hσ
end PELOriginalChartPeriodMetric318
