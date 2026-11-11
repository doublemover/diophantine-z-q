module
public import PELMaximalLocalOrbit318
public section
noncomputable section
namespace PELMaximalSquaredLocalFibers318
open QuaternionicJointPeriodTopology318 PELUnlevelledComplexBase318
open PELOriginalMaximalQuotient318 PELMaximalLocalOrbit318 PELOriginalBranchLabels318
open PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318 PELUnlevelledNormalizerAction318
open PELNontrivialFixedTraceZero318 PELCoarseInertiaCoordinate318 PELInertiaSquaredCoordinate318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1800000
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

/-- On an actual OPEN neighborhood of every labeled fixed point, fibers
of the full positive-normalizer quotient are exactly fibers of the literal
squared original holomorphic chart. The local domain is constructed. -/
theorem original_squared_quotient_fibers (i : Fin 5) (τ : HalfPlane)
    (hp : PELUnlevelledComplexBase318.projection τ∈fixedLocus i) :
    ∃ U : Set UnlevelledBase,IsOpen U ∧ PELUnlevelledComplexBase318.projection τ∈U ∧
      U⊆(inertiaChart τ).source ∧
      ∀ x∈U,∀ y∈U,
        PELOriginalMaximalQuotient318.projection x=PELOriginalMaximalQuotient318.projection y ↔
        squaredCoordinate τ x=squaredCoordinate τ y := by
  let p := PELUnlevelledComplexBase318.projection τ
  obtain ⟨n,hn,ht,hpar⟩ := fixed_trace_zero (InertiaLabels318.fiveLabels i)
    (InertiaLabels318.five_labels_nonzero i) τ hp
  have ha (x : UnlevelledBase) : coarseAction n x=
      Multiplicative.ofAdd (InertiaLabels318.fiveLabels i) • x := by
    rw [PELFullNormalizerAction318.actual_action_factorization,hpar]
  have hnp : coarseAction n p=p := by rw [coarseAction_square,hn]
  obtain ⟨V,hV,hrel⟩ := local_orbit_relation i p hp
  have hsrc : (inertiaChart τ).source∈𝓝 p :=
    (inertiaChart τ).open_source.mem_nhds (chart_center_source τ)
  have hnsrc : {x | coarseAction n x∈(inertiaChart τ).source}∈𝓝 p := by
    have hcont := (coarseAction_holomorphic n p).continuousAt
    change Tendsto (coarseAction n) (𝓝 p) (𝓝 (coarseAction n p)) at hcont
    rw [hnp] at hcont
    exact hcont.eventually hsrc
  let S : Set UnlevelledBase := {x | x∈V ∧ x∈(inertiaChart τ).source ∧
    coarseAction n x∈(inertiaChart τ).source ∧
    inertiaChart τ (coarseAction n x)= -inertiaChart τ x}
  have hS : S∈𝓝 p := by
    filter_upwards [hV,hsrc,hnsrc,local_negation n τ hn ht] with x hx hcx hnx hsign
    exact ⟨hx,hcx,hnx,hsign⟩
  refine ⟨interior S,isOpen_interior,mem_interior_iff_mem_nhds.mpr hS,?_,?_⟩
  · intro x hx
    exact (interior_subset hx).2.1
  · intro x hx y hy
    have hxS : x∈S := interior_subset hx
    have hyS : y∈S := interior_subset hy
    have hsq := squared_fiber_iff n τ x y hxS.2.1 hyS.2.1 hyS.2.2.1 hyS.2.2.2
    rw [ha y] at hsq
    exact (hrel x hxS.1 y hyS.1).trans hsq.symm
end PELMaximalSquaredLocalFibers318
