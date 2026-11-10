module
public import PELMaximalComplexAtlas318
public section
noncomputable section
namespace PELOriginalMaximalCharts318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318
open PELMaximalTransitionHolomorphy318 PELMaximalComplexAtlas318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1700000
local instance : ChartedSpace ℂ MaximalBase := maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase := maximal_manifold

/-- Every original regular or squared quotient chart, not only the
classically chosen chart, is holomorphic for the actual constructed atlas. -/
theorem original_chart_holomorphic (e : OpenPartialHomeomorph MaximalBase ℂ)
    (he : OriginalChart e) (q : MaximalBase) (hq : q∈e.source) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e q := by
  let A := chosenChart q
  have hAq : q∈A.source := chosenChart_center q
  have hA : A∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω MaximalBase :=
    IsManifold.subset_maximalAtlas ⟨q,rfl⟩
  have ht := original_transition e A he (chosenChart_original q) q hq hAq
  have hT : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun z => e (A.symm z)) (A q) :=
    contMDiffAt_iff_contDiffAt.mpr ht.contDiffAt
  have h := hT.comp q (contMDiffAt_of_mem_maximalAtlas hA hAq)
  apply h.congr_of_eventuallyEq
  filter_upwards [A.open_source.mem_nhds hAq] with x hx
  exact congrArg e (A.left_inv hx).symm

theorem original_inverse_holomorphic (e : OpenPartialHomeomorph MaximalBase ℂ)
    (he : OriginalChart e) (z : ℂ) (hz : z∈e.target) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm z := by
  let q := e.symm z
  let A := chosenChart q
  have hAq : q∈A.source := chosenChart_center q
  have hA : A∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω MaximalBase :=
    IsManifold.subset_maximalAtlas ⟨q,rfl⟩
  have ht := original_transition A e (chosenChart_original q) he q hAq (e.map_target hz)
  have ht' : AnalyticAt ℂ (fun w => A (e.symm w)) z := by
    simpa only [q,e.right_inv hz] using ht
  have hT : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w => A (e.symm w)) z :=
    contMDiffAt_iff_contDiffAt.mpr ht'.contDiffAt
  have h := (contMDiffAt_symm_of_mem_maximalAtlas hA (A.map_source hAq)).comp z hT
  apply h.congr_of_eventuallyEq
  filter_upwards [(e.continuousAt_symm hz).tendsto.eventually
    (A.open_source.mem_nhds hAq)] with w hw
  exact (A.left_inv hw).symm

theorem original_chart_maximal (e : OpenPartialHomeomorph MaximalBase ℂ)
    (he : OriginalChart e) : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω MaximalBase := by
  apply e.mem_maximalAtlas_of_contMDiffOn
  · exact fun q hq => (original_chart_holomorphic e he q hq).contMDiffWithinAt
  · exact fun z hz => (original_inverse_holomorphic e he z hz).contMDiffWithinAt
end PELOriginalMaximalCharts318
