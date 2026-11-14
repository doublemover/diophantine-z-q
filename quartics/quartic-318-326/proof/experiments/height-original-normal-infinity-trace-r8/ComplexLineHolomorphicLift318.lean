module
public import PELOriginalDoublingHolomorphy318
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Analysis.Convex.Contractible
public section
noncomputable section
namespace ComplexLineHolomorphicLift318
open ComplexLineLatticeAtlas318 ComplexLineLatticeMaps318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 2600000
variable (L : AddSubgroup ℂ) [DiscreteTopology L]
local instance : ChartedSpace ℂ (Quotient L) := chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Quotient L) := complex_manifold L

/-- Every holomorphic endomorphism of the ACTUAL complex-line period
quotient has an entire lift after composition with its original covering.
The lift is constructed by simply connected covering theory, then proved
holomorphic through the SAME quotient inverse charts. -/
theorem exists_entire_lift (f : Quotient L→Quotient L)
    (hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f) :
    ∃ F : ℂ→ℂ,ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F ∧
      ∀ z,projection L (F z)=f (projection L z) := by
  let g : C(ℂ,Quotient L) := ⟨f ∘ projection L,
    hf.continuous.comp (projection_contMDiff L).continuous⟩
  obtain ⟨a,ha⟩ := quotient_surjective L (g 0)
  obtain ⟨F,⟨_,hF⟩,_⟩ :=
    (quotient_covering L).isCoveringMap.existsUnique_continuousMap_lifts g (0:ℂ) a ha
  have hmap (z : ℂ) : projection L (F z)=f (projection L z) := congrFun hF z
  refine ⟨F,?_,hmap⟩
  intro z
  let c := localChart L (F z)
  have hc0 : projection L (F z)∈c.source := localChart_center L (F z)
  have hc := contMDiffAt_of_mem_maximalAtlas (chart_maximal L (F z)) hc0
  have hc' : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω c (f (projection L z)) := by
    rw [←hmap z]
    exact hc
  have hlocal := hc'.comp z ((hf _).comp z (projection_contMDiff L z))
  apply hlocal.congr_of_eventuallyEq
  have ht : F z∈c.target := (quotient_localHomeomorph L).self_mem_localInverseAt_target
  filter_upwards [F.continuous.continuousAt.eventually (c.open_target.mem_nhds ht)] with w hw
  have he := c.right_inv hw
  rw [localChart_symm,hmap] at he
  exact he.symm
end ComplexLineHolomorphicLift318
