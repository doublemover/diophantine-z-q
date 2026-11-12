module
public import ComplexTorusCoverLift318
public import ComplexCurveContinuousLift318
public section
noncomputable section
namespace ComplexTorusCoverHolomorphicLift318
open Set Filter Topology
open scoped Manifold ContDiff
open ComplexLineLatticeAtlas318 ComplexTorusCoverLift318
variable (L:AddSubgroup ℂ) [DiscreteTopology L]
variable {E:Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ,ℂ) ω E]
local instance : ChartedSpace ℂ (Quotient L):=chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Quotient L):=complex_manifold L
variable (p:E→Quotient L) (cov:IsCoveringMap p) (e₀:E) (he:p e₀=projection L 0)

/-- The constructed universal lift is holomorphic in the specified
ORIGINAL source atlas. Continuity and the lift equation were proved by
covering-space lifting; the local inverse theorem derives nonvanishing
rather than requiring an extra differential assumption. -/
theorem lift_holomorphic (hp:ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω p) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (lift L p cov e₀ he) := by
  intro z
  apply ComplexCurveContinuousLift318.lift_at p univ
    cov.isLocalHomeomorph.isLocalHomeomorphOn
    (lift L p cov e₀ he) (projection L) z (mem_univ _) (hp _)
    (lift L p cov e₀ he).continuous.continuousAt
    (ComplexLineLatticeMaps318.projection_contMDiff L z)
  exact Eventually.of_forall (lift_projection L p cov e₀ he)
end ComplexTorusCoverHolomorphicLift318
