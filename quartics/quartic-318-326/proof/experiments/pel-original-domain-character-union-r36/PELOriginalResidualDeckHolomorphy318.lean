module
public import PELOriginalResidualDeckFibers318
public section
noncomputable section
namespace PELOriginalResidualDeckHolomorphy318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalCharacterComplexAtlas318
open PELOriginalInvolutionTower318 PELOriginalInvolutionLocalCover318
open PELOriginalInvolutionComplexAtlas318 PELOriginalResidualDeckAction318
open PELOriginalResidualDeckFibers318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 2400000
variable (i : Fin 4)
local instance : ChartedSpace ℂ PELUnlevelledComplexBase318.UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω PELUnlevelledComplexBase318.UnlevelledBase := unlevelled_manifold
local instance : ChartedSpace ℂ (CharacterBase i) := PELOriginalCharacterTopologicalAtlas318.characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i) := character_manifold i
local instance : ChartedSpace ℂ (InvolutionBase i) := involutionCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (InvolutionBase i) := involution_manifold i

lemma kernelMap_continuous (k : (character i).ker) : Continuous (kernelMap i k) :=
  ((toInvolution_continuous i).comp
    (PELOriginalElementaryAction318.original_action_holomorphic (k:Labels)).continuous).quotient_lift _
lemma deck_continuous (g : Deck i) : Continuous (fun y : InvolutionBase i => g • y) := by
  obtain ⟨k,rfl⟩ := deckMap_surjective i g
  exact kernelMap_continuous i k

/-- The actual free residual transformations are holomorphic on the SAME
involution-quotient atlas, using its actual local sheets over the character
surface. No genus-one uniformization or algebraization is invoked. -/
theorem deck_holomorphic (g : Deck i) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y : InvolutionBase i => g • y) := by
  intro p
  let q := g • p
  let e := sheetChart i q
  let A := chartAt ℂ (toCharacterBase i q)
  have hq := sheetChart_center i q
  have hbase : toCharacterBase i q=toCharacterBase i p := deck_over_base i g p
  have hA := contMDiffAt_of_mem_maximalAtlas
    (IsManifold.chart_mem_maximalAtlas (toCharacterBase i q)) (mem_chart_source ℂ _)
  have hA' : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω A (toCharacterBase i p) := by
    rw [←hbase]
    exact hA
  have hAC := hA'.comp p (toCharacterBase_holomorphic i p)
  have hI := contMDiffAt_symm_of_mem_maximalAtlas (sheetChart_maximal i q) (e.map_source hq)
  have hI' : ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω e.symm (A (toCharacterBase i p)) := by
    simpa only [sheetChart_value i q q hq,hbase] using hI
  apply (hI'.comp p hAC).congr_of_eventuallyEq
  filter_upwards [(deck_continuous i g).continuousAt.tendsto.eventually
    (e.open_source.mem_nhds hq)] with y hy
  have hv := sheetChart_value i q (g • y) hy
  rw [deck_over_base] at hv
  exact (e.left_inv hy).symm.trans (congrArg e.symm hv)

/-- The inverse is the SAME original residual transformation because its
square is one. Both directions are holomorphic on the unchanged surface. -/
theorem deck_biholomorphic (g : Deck i) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y : InvolutionBase i => g • y) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun y : InvolutionBase i => g⁻¹ • y) :=
  ⟨deck_holomorphic i g,deck_holomorphic i g⁻¹⟩
end PELOriginalResidualDeckHolomorphy318
