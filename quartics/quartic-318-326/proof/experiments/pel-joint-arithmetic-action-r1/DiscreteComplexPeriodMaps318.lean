module
public import DiscreteComplexPeriodAtlas318
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public section
noncomputable section
namespace DiscreteComplexPeriodMaps318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1000000
variable (L : AddSubgroup ComplexVectors) [DiscreteTopology L]
local instance : ChartedSpace ComplexVectors (Quotient L) := chartedSpace L
local instance : IsManifold 𝓘(ℂ,ComplexVectors) ω (Quotient L) := complex_manifold L

theorem chart_maximal (a : ComplexVectors) :
    localChart L a∈IsManifold.maximalAtlas 𝓘(ℂ,ComplexVectors) ω (Quotient L) :=
  IsManifold.subset_maximalAtlas ⟨a,rfl⟩

/-- The original quotient projection is holomorphic for the atlas actually
constructed from this projection, not an unrelated complex torus structure. -/
theorem projection_contMDiff :
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω (projection L) := by
  intro a
  have h := contMDiffAt_symm_of_mem_maximalAtlas (chart_maximal L a)
    (quotient_localHomeomorph L).self_mem_localInverseAt_target
  simpa only [show ((localChart L a).symm:ComplexVectors→Quotient L)=projection L from
    funext (localChart_symm L a)] using h

/-- An actual descended complex-linear map is holomorphic. The quotient
commuting square is required for the exact maps and all representatives. -/
theorem descended_linear_contMDiff (A : ComplexVectors →ₗ[ℂ] ComplexVectors)
    (f : Quotient L → Quotient L)
    (hf : ∀ z, f (projection L z)=projection L (A z)) :
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω f := by
  intro p
  obtain ⟨a,rfl⟩ := quotient_surjective L p
  have hA : ContMDiffAt 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω A a :=
    contMDiffAt_iff_contDiffAt.mpr A.toContinuousLinearMap.contDiff.contDiffAt
  have hlocal : ContMDiffAt 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω
      (f ∘ (localChart L a).symm) a := by
    apply ((projection_contMDiff L (A a)).comp a hA).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun z => by
      change f ((localChart L a).symm z)=projection L (A z)
      rw [localChart_symm,hf])
  have hp := localChart_center L a
  have hv : localChart L a (projection L a)=a :=
    (quotient_localHomeomorph L).localInverseAt_apply_self
  have hc := contMDiffAt_of_mem_maximalAtlas (chart_maximal L a) hp
  have hlocal' : ContMDiffAt 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω
      (f ∘ (localChart L a).symm) (localChart L a (projection L a)) := by
    rwa [hv]
  apply (hlocal'.comp _ hc).congr_of_eventuallyEq
  filter_upwards [(localChart L a).open_source.mem_nhds hp] with q hq
  simp only [Function.comp_apply,(localChart L a).left_inv hq]
end DiscreteComplexPeriodMaps318
