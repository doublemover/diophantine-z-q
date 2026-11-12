module
public import PELOriginalCharacterComplexAtlas318
public section
noncomputable section
namespace PELOriginalCharacterCharts318
open PELUnlevelledComplexBase318 PELOriginalCharacterQuotient318 PELOriginalCharacterTopologicalAtlas318
open PELOriginalCharacterTransition318 PELOriginalCharacterComplexAtlas318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1700000
variable (i : Fin 4)
local instance : ChartedSpace ℂ (CharacterBase i) := characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i) := character_manifold i

/-- Every original regular or squared quotient chart, not only the
classically chosen chart, is holomorphic for the actual constructed atlas. -/
theorem original_chart_holomorphic (e : OpenPartialHomeomorph (CharacterBase i) ℂ)
    (he : OriginalChart i e) (q : (CharacterBase i)) (hq : q∈e.source) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e q := by
  let A := chosenChart i q
  have hAq : q∈A.source := chosenChart_center i q
  have hA : A∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (CharacterBase i) :=
    IsManifold.subset_maximalAtlas ⟨q,rfl⟩
  have ht := original_transition i e A he (chosenChart_original i q) q hq hAq
  have hT : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun z => e (A.symm z)) (A q) :=
    contMDiffAt_iff_contDiffAt.mpr ht.contDiffAt
  have h := hT.comp q (contMDiffAt_of_mem_maximalAtlas hA hAq)
  apply h.congr_of_eventuallyEq
  filter_upwards [A.open_source.mem_nhds hAq] with x hx
  exact congrArg e (A.left_inv hx).symm

theorem original_inverse_holomorphic (e : OpenPartialHomeomorph (CharacterBase i) ℂ)
    (he : OriginalChart i e) (z : ℂ) (hz : z∈e.target) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm z := by
  let q := e.symm z
  let A := chosenChart i q
  have hAq : q∈A.source := chosenChart_center i q
  have hA : A∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (CharacterBase i) :=
    IsManifold.subset_maximalAtlas ⟨q,rfl⟩
  have ht := original_transition i A e (chosenChart_original i q) he q hAq (e.map_target hz)
  have ht' : AnalyticAt ℂ (fun w => A (e.symm w)) z := by
    simpa only [q,e.right_inv hz] using ht
  have hT : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun w => A (e.symm w)) z :=
    contMDiffAt_iff_contDiffAt.mpr ht'.contDiffAt
  have h := (contMDiffAt_symm_of_mem_maximalAtlas hA (A.map_source hAq)).comp z hT
  apply h.congr_of_eventuallyEq
  filter_upwards [(e.continuousAt_symm hz).tendsto.eventually
    (A.open_source.mem_nhds hAq)] with w hw
  exact (A.left_inv hw).symm

theorem original_chart_maximal (e : OpenPartialHomeomorph (CharacterBase i) ℂ)
    (he : OriginalChart i e) : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (CharacterBase i) := by
  apply e.mem_maximalAtlas_of_contMDiffOn
  · exact fun q hq => (original_chart_holomorphic i e he q hq).contMDiffWithinAt
  · exact fun z hz => (original_inverse_holomorphic i e he z hz).contMDiffWithinAt
end PELOriginalCharacterCharts318
