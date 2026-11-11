module
public import DiscreteComplexPeriodMaps318
public section
noncomputable section
namespace DiscreteComplexPeriodEquiv318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318 DiscreteComplexPeriodMaps318
open Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1000000
variable (L K : AddSubgroup ComplexVectors) [DiscreteTopology L] [DiscreteTopology K]
local instance : ChartedSpace ComplexVectors (Quotient L) := chartedSpace L
local instance : ChartedSpace ComplexVectors (Quotient K) := chartedSpace K
local instance : IsManifold 𝓘(ℂ,ComplexVectors) ω (Quotient L) := complex_manifold L
local instance : IsManifold 𝓘(ℂ,ComplexVectors) ω (Quotient K) := complex_manifold K

/-- Holomorphy across two DIFFERENT original lattice quotients, witnessed
by the exact projection square rather than an unproved quotient atlas match. -/
theorem descended_linear_between (A : ComplexVectors →ₗ[ℂ] ComplexVectors)
    (f : Quotient L → Quotient K)
    (hf : ∀ z, f (projection L z)=projection K (A z)) :
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω f := by
  intro p
  obtain ⟨a,rfl⟩ := quotient_surjective L p
  have hA : ContMDiffAt 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω A a :=
    contMDiffAt_iff_contDiffAt.mpr A.toContinuousLinearMap.contDiff.contDiffAt
  have hlocal : ContMDiffAt 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω
      (f ∘ (localChart L a).symm) a := by
    apply ((projection_contMDiff K (A a)).comp a hA).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun z => by
      change f ((localChart L a).symm z)=projection K (A z)
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

/-- A full lattice equality transports an actual complex-linear equivalence
in both holomorphic directions for the previously constructed quotient atlases. -/
theorem congr_holomorphic (e : ComplexVectors ≃ₗ[ℂ] ComplexVectors)
    (he : L.map e.toAddEquiv.toAddMonoidHom=K) :
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω
      (QuotientAddGroup.congr L K e.toAddEquiv he) :=
  descended_linear_between L K e.toLinearMap _ (fun _ => rfl)

theorem congr_symm_holomorphic (e : ComplexVectors ≃ₗ[ℂ] ComplexVectors)
    (he : L.map e.toAddEquiv.toAddMonoidHom=K) :
    ContMDiff 𝓘(ℂ,ComplexVectors) 𝓘(ℂ,ComplexVectors) ω
      (QuotientAddGroup.congr L K e.toAddEquiv he).symm :=
  descended_linear_between K L e.symm.toLinearMap _ (fun _ => rfl)
end DiscreteComplexPeriodEquiv318
