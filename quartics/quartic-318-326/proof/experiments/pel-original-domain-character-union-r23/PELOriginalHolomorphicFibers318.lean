module
public import PELHolomorphicFamilyProjection318
public section
noncomputable section
namespace PELOriginalHolomorphicFibers318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318
open PELJointPeriodFamily318 PELJointPeriodDeck318 PELJointComplexAtlas318 PELComplexPeriodSurface318
open PELHolomorphicFamilyProjection318 DiscreteComplexPeriodAtlas318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1400000
local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold

@[expose] def verticalLinear : ComplexVectors →ₗ[ℂ] Ambient where
  toFun z := (0,z)
  map_add' z w := by simp
  map_smul' a z := by simp

@[expose] def vertical (τ : HalfPlane) (z : ComplexVectors) : Ambient := (τ,z)

theorem vertical_contMDiff (τ : HalfPlane) :
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,Ambient) ω (vertical τ) := by
  have h : ContDiff ℂ ω (fun z => verticalLinear z+((τ:ℂ),0)) :=
    verticalLinear.toContinuousLinearMap.contDiff.add contDiff_const
  apply contMDiff_iff_contDiff.mpr
  simpa only [vertical,verticalLinear,LinearMap.coe_mk,AddHom.coe_mk,
    Prod.mk_add_mk,zero_add,add_zero] using h

theorem familyChart_at_center (b : Cover) : familyChart b (familyProjection b)=ambient b := by
  rw [familyChart_apply]
  congr 1
  exact familyProjection_localHomeomorph.localInverseAt_apply_self

theorem inverseChart_vertical (b : Cover) (τ : HalfPlane) (z : ComplexVectors) :
    (familyChart b).symm (vertical τ z)=familyProjection (τ,z) := by
  rw [familyChart_symm]
  congr 1
  exact ambientChart.left_inv (ambientChart_source (τ,z))

/-- The covering map of each original surface is holomorphic into the
JOINT threefold, not just into its separately constructed quotient surface. -/
theorem fiber_uniformization_holomorphic (τ : HalfPlane) :
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,Ambient) ω (fun z => familyProjection (τ,z)) := by
  intro z
  have ht : vertical τ z∈(familyChart (τ,z)).target := by
    have h := (familyChart (τ,z)).map_source (familyChart_center (τ,z))
    rwa [familyChart_at_center] at h
  have hi := contMDiffAt_symm_of_mem_maximalAtlas (familyChart_maximal (τ,z)) ht
  apply (hi.comp z (vertical_contMDiff τ z)).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun w => (inverseChart_vertical (τ,z) τ w).symm)

variable (τ : HalfPlane)
local instance : DiscreteTopology (Periods τ) :=
  PELOriginalPeriodLattice318.original_discrete τ τ.property
local instance : ChartedSpace ComplexVectors (Surface τ) := surfaceCharts τ τ.property
local instance : IsManifold 𝓘(ℂ,ComplexVectors) ω (Surface τ) := surface_manifold τ τ.property

@[expose] def originalFiberInclusion (p : Surface τ) : Total :=
  (originalFiberHomeomorph τ p).val

theorem originalFiberInclusion_mk (z : ComplexVectors) :
    originalFiberInclusion τ (QuotientAddGroup.mk' (Periods τ) z)=familyProjection (τ,z) :=
  original_fiber_projection τ z

/-- The literal fiber comparison uses the ORIGINAL complex surface atlas
and is holomorphic into the genuine joint family. -/
theorem originalFiberInclusion_holomorphic :
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,Ambient) ω (originalFiberInclusion τ) := by
  intro p
  obtain ⟨z,rfl⟩ := quotient_surjective (Periods τ) p
  have hlocal : ContMDiffAt 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,Ambient) ω
      (originalFiberInclusion τ ∘ (localChart (Periods τ) z).symm) z := by
    apply (fiber_uniformization_holomorphic τ z).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun w => by
      change originalFiberInclusion τ ((localChart (Periods τ) z).symm w)=_
      rw [localChart_symm]
      exact originalFiberInclusion_mk τ w)
  have hp := localChart_center (Periods τ) z
  have hz : localChart (Periods τ) z (projection (Periods τ) z)=z :=
    (quotient_localHomeomorph (Periods τ)).localInverseAt_apply_self
  have hlocal' : ContMDiffAt 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,Ambient) ω
      (originalFiberInclusion τ ∘ (localChart (Periods τ) z).symm)
      (localChart (Periods τ) z (projection (Periods τ) z)) := by rwa [hz]
  have hc := contMDiffAt_of_mem_maximalAtlas
    (DiscreteComplexPeriodMaps318.chart_maximal (Periods τ) z) hp
  apply (hlocal'.comp _ hc).congr_of_eventuallyEq
  filter_upwards [(localChart (Periods τ) z).open_source.mem_nhds hp] with q hq
  simp only [Function.comp_apply,(localChart (Periods τ) z).left_inv hq]
end PELOriginalHolomorphicFibers318
