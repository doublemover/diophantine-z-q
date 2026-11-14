module
public import ComplexCurvePartialInverse318
public import Mathlib.Topology.IsLocalHomeomorph
public section
noncomputable section
namespace ComplexCurveHolomorphicDescent318
open Set Filter
open scoped Topology Manifold ContDiff
variable {M N P:Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [ChartedSpace ℂ M] [ChartedSpace ℂ N] [ChartedSpace ℂ P]
  [IsManifold 𝓘(ℂ,ℂ) ω M] [IsManifold 𝓘(ℂ,ℂ) ω N] [IsManifold 𝓘(ℂ,ℂ) ω P]

/-- Descend a holomorphic composite through a genuine holomorphic local
homeomorphism. Its inverse regularity is proved in the given atlases. -/
theorem at_image (q:M→N) (F:N→P) (S:Set M) (hlocal:IsLocalHomeomorphOn q S)
    (p:M) (hp:p∈S) (hq:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω q p)
    (hF:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (F ∘ q) p):
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F (q p):=by
  obtain ⟨e,hpe,heq⟩:=hlocal p hp
  have he:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e p:=by rwa [←heq]
  have hinv:=ComplexCurvePartialInverse318.inverse_at e p hpe he
  have hcenter:e.symm (q p)=p:=by rw [heq,e.left_inv hpe]
  rw [←heq] at hinv
  have hc:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (F ∘ q) (e.symm (q p)):=by
    rwa [hcenter]
  apply (hc.comp (q p) hinv).congr_of_eventuallyEq
  have hn:e.target∈𝓝 (q p):=by rw [heq];exact e.open_target.mem_nhds (e.map_source hpe)
  filter_upwards [hn] with z hz
  change F z=F (q (e.symm z))
  rw [heq,e.right_inv hz]
end ComplexCurveHolomorphicDescent318
