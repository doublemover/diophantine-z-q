module
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public section
noncomputable section
namespace HolomorphicHomeomorphChartTransport318
open Set
open scoped Manifold ContDiff
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace ℂ M] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ,ℂ) ω M] [IsManifold 𝓘(ℂ,ℂ) ω N]

/-- Pulling an actual chart through a given biholomorphism preserves
membership in the genuine maximal atlas, with both original structures retained. -/
theorem maximal (h : M ≃ₜ N)
    (hh : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω h)
    (hi : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω h.symm)
    (e : OpenPartialHomeomorph N ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω N) :
    h.toOpenPartialHomeomorph.trans e ∈ IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω M := by
  apply (IsManifold.mem_maximalAtlas_iff_contMDiffOn _).mpr
  constructor
  · intro x hx
    exact ((contMDiffAt_of_mem_maximalAtlas he hx.2).comp x (hh x)).contMDiffWithinAt
  · intro z hz
    exact ((hi _).comp z (contMDiffAt_symm_of_mem_maximalAtlas he hz.1)).contMDiffWithinAt
end HolomorphicHomeomorphChartTransport318
