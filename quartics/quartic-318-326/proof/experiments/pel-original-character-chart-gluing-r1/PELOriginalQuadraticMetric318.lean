module
public import PELOriginalPoincareAtlas318
public import PeterssonSectionNorm318
public section
noncomputable section
namespace PELOriginalQuadraticMetric318
open PELUnlevelledComplexBase318 PELOriginalPoincareAtlas318 PeterssonSectionNorm318
open scoped Manifold ContDiff
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

/-- The exact factor2 convention of the quantitative Petersson norm is
coordinate invariant under the genuine original cotangent-square cocycle. -/
theorem chart_norm_invariant (e d : OpenPartialHomeomorph UnlevelledBase ℂ)
    (p : UnlevelledBase) (hp : p ∈ e.source) (hq : p ∈ d.source)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase) (q : ℂ) :
    quadraticNorm (chartDensity e p) (q * (deriv (coordinateChange e d p) 0)^2) =
      quadraticNorm (chartDensity d p) q := by
  have hpe := chartDensity_positive e p hp he
  have hpd := chartDensity_positive d p hq hd
  have ht := chartDensity_transition e d p hp hq he hd
  have hder : deriv (coordinateChange e d p) 0 ≠ 0 := by
    intro hz
    rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero] at ht
    exact (ne_of_gt hpe) ht
  rw [quadraticNorm_formula _ hpe,quadraticNorm_formula _ hpd,ht,norm_mul,norm_pow]
  have hn := norm_ne_zero_iff.mpr hder
  field_simp [hn,hpd.ne']

/-- Multiplying the SAME quadratic differential by the original integral
normalizing scalar retains that scalar in every chart; no frame is replaced. -/
theorem scaled_chart_norm_invariant (e d : OpenPartialHomeomorph UnlevelledBase ℂ)
    (p : UnlevelledBase) (hp : p ∈ e.source) (hq : p ∈ d.source)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω UnlevelledBase) (a q : ℂ) :
    quadraticNorm (chartDensity e p) (a * (q * (deriv (coordinateChange e d p) 0)^2)) =
      quadraticNorm (chartDensity d p) (a * q) := by
  rw [quadraticNorm_mul,quadraticNorm_mul,chart_norm_invariant e d p hp hq he hd]
end PELOriginalQuadraticMetric318
