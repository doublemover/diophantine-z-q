module
public import PELJointComplexAtlas318
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public section
noncomputable section
namespace PELHolomorphicFamilyProjection318
open QuaternionicRealPeriod318 QuaternionicJointPeriodTopology318
open PELJointPeriodFamily318 PELJointPeriodDeck318 PELJointComplexAtlas318 PELComplexPeriodSurface318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1400000
local instance : ChartedSpace Ambient Total := totalCharts
local instance : IsManifold 𝓘(ℂ,Ambient) ω Total := total_manifold

@[expose] def baseValue (p : Total) : ℂ := p.1

theorem baseValue_positive (p : Total) : 0<(baseValue p).im := p.1.property

theorem familyChart_maximal (a : Cover) :
    familyChart a∈IsManifold.maximalAtlas 𝓘(ℂ,Ambient) ω Total :=
  IsManifold.subset_maximalAtlas ⟨a,rfl⟩

/-- In the ACTUAL joint complex charts the base map is literally the first
complex coordinate, so its transverse coordinate is not an assumed period map. -/
theorem base_in_chart (a : Cover) (z : Ambient) (hz : z∈ambientChart.target) :
    baseValue ((familyChart a).symm z)=z.1 := by
  rw [familyChart_symm]
  exact congrArg Prod.fst (ambientChart.right_inv hz)

theorem base_chart_contMDiffAt (a : Cover) (z : Ambient) (hz : z∈ambientChart.target) :
    ContMDiffAt 𝓘(ℂ,Ambient) 𝓘(ℂ,ℂ) ω (baseValue ∘ (familyChart a).symm) z := by
  have hf : ContMDiffAt 𝓘(ℂ,Ambient) 𝓘(ℂ,ℂ) ω Prod.fst z :=
    contMDiffAt_iff_contDiffAt.mpr (ContinuousLinearMap.fst ℂ ℂ ComplexVectors).contDiff.contDiffAt
  apply hf.congr_of_eventuallyEq
  filter_upwards [ambientChart.open_target.mem_nhds hz] with w hw
  exact base_in_chart a w hw

/-- The actual joint family has a holomorphic base projection to the upper
half-plane open in C. Fiber compactness alone was not used to infer this. -/
theorem base_holomorphic : ContMDiff 𝓘(ℂ,Ambient) 𝓘(ℂ,ℂ) ω baseValue := by
  intro p
  obtain ⟨a,rfl⟩ := familyProjection_surjective p
  have hp := familyChart_center a
  have ht := familyChart_target_upper a _ ((familyChart a).map_source hp)
  have hlocal := base_chart_contMDiffAt a _ ht
  have hc := contMDiffAt_of_mem_maximalAtlas (familyChart_maximal a) hp
  apply (hlocal.comp _ hc).congr_of_eventuallyEq
  filter_upwards [(familyChart a).open_source.mem_nhds hp] with q hq
  simp only [Function.comp_apply,(familyChart a).left_inv hq]

/-- A literal fiber of the joint total space, rather than an independently
named surface that is only said to correspond to that fiber. -/
abbrev Fiber (τ : HalfPlane) := {p : Total // p.1=τ}

@[expose] def originalFiberHomeomorph (τ : HalfPlane) : Surface τ ≃ₜ Fiber τ where
  toFun p := ⟨(τ,fiberHomeomorph τ p),rfl⟩
  invFun p := (fiberHomeomorph τ).symm p.val.2
  left_inv p := (fiberHomeomorph τ).symm_apply_apply p
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext p.property.symm
    exact (fiberHomeomorph τ).apply_symm_apply p.val.2
  continuous_toFun :=
    (continuous_const.prodMk (fiberHomeomorph τ).continuous).subtype_mk _
  continuous_invFun := (fiberHomeomorph τ).symm.continuous.comp
    (continuous_snd.comp continuous_subtype_val)

theorem original_fiber_projection (τ : HalfPlane) (z : ComplexVectors) :
    (originalFiberHomeomorph τ (QuotientAddGroup.mk' (Periods τ) z)).val=
      familyProjection (τ,z) := (projection_fiber τ z).symm

/-- Compactness is on every literal fiber of the holomorphic joint family,
with the exact original surface comparison retained. -/
theorem original_fiber_compact (τ : HalfPlane) : CompactSpace (Fiber τ) := by
  letI : CompactSpace (Surface τ) := fiber_compact τ
  exact (originalFiberHomeomorph τ).compactSpace
end PELHolomorphicFamilyProjection318
