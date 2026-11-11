module
public import ComplexCurvePartialInverse318
public import Mathlib.Topology.IsLocalHomeomorph
public section
noncomputable section
namespace ComplexCurveContinuousLift318
open Set Filter
open scoped Topology Manifold ContDiff
variable {M N:Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace ℂ M] [ChartedSpace ℂ N]
  [IsManifold 𝓘(ℂ,ℂ) ω M] [IsManifold 𝓘(ℂ,ℂ) ω N]

/-- A continuous lift through a holomorphic LOCAL homeomorphism of the
original complex curves is holomorphic. The inverse is constructed in the
original charts; a derivative condition is derived, never supplied. -/
theorem lift_at (p:M→N) (T:Set M) (hlocal:IsLocalHomeomorphOn p T)
    (s:ℂ→M) (g:ℂ→N) (z:ℂ) (hz:s z∈T)
    (hp:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p (s z))
    (hs:ContinuousAt s z) (hg:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω g z)
    (he:(p ∘ s)=ᶠ[𝓝 z] g) : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω s z := by
  obtain ⟨e,hse,hpeq⟩:=hlocal (s z) hz
  have hph:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e (s z):=by simpa only [←hpeq] using hp
  have hinv:=ComplexCurvePartialInverse318.inverse_at e (s z) hse hph
  have hez:e (s z)=g z := by
    rw [←hpeq]
    exact he.self_of_nhds
  rw [hez] at hinv
  apply (hinv.comp z hg).congr_of_eventuallyEq
  filter_upwards [hs.eventually (e.open_source.mem_nhds hse),he] with w hw hwe
  change s w=e.symm (g w)
  rw [←hwe,hpeq,e.left_inv hw]
end ComplexCurveContinuousLift318
