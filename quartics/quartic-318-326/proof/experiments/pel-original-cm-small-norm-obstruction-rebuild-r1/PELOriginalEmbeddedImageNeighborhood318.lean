module
public import PELOriginalLevelThreeAmbientImage318
public section
noncomputable section
namespace PELOriginalEmbeddedImageNeighborhood318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalLevelThreeLocalImage318
open PELOriginalPolarizationTransitions318 PELOriginalAllLevelProjectiveMap318
open DiscreteComplexPeriodAtlas318 ComplexProjectiveQuotientTopology318 Set Topology
variable (τ:ℂ) (hτ:0<τ.im)
local instance discretePeriods:DiscreteTopology (P τ):=
  PELOriginalPeriodLattice318.original_discrete τ hτ
local instance targetTopology:TopologicalSpace (Target 1):=topology (Label 3)

/-- The original closed embedding isolates ANY genuine open source
patch by an actual ambient projective open set. This prevents distant
parts of the image from being silently omitted by a local graph. -/
lemma isolate_source_patch (U:Set (Base τ)) (hU:IsOpen U):
    ∃O:Set (Target 1),IsOpen O ∧ projectiveMap τ hτ 1 ⁻¹' O=U ∧
      Set.range (projectiveMap τ hτ 1)∩O=projectiveMap τ hτ 1 '' U:=by
  obtain ⟨O,hO,hpre⟩:=
    (PELOriginalLevelThreeClosedEmbedding318.closed_embedding τ hτ).isEmbedding.isInducing.isOpen_iff.mp hU
  refine ⟨O,hO,?_,?_⟩
  · exact hpre
  · ext y
    constructor
    · rintro ⟨⟨q,rfl⟩,hq⟩
      exact ⟨q,by rw [←hpre];exact hq,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      refine ⟨⟨q,rfl⟩,?_⟩
      change q∈projectiveMap τ hτ 1 ⁻¹' O
      rwa [hpre]

variable (x:ComplexVectors) (j:Label 3) (hj:value τ hτ 3 j x≠0)
@[expose] def parameterDomain (W:Set ComplexVectors):Set ComplexVectors:=
  (parameterChart τ hτ x j hj).source ∩ (parameterChart τ hτ x j hj) ⁻¹' W
@[expose] def sourcePatch (W:Set ComplexVectors):Set (Base τ):=
  (DiscreteComplexPeriodAtlas318.localChart (P τ) x).symm '' parameterDomain τ hτ x j hj W
lemma parameterDomain_subset (W:Set ComplexVectors)
    (hU:∀w∈W,(parameterChart τ hτ x j hj).symm w∈originalChartDomain τ hτ x j):
    parameterDomain τ hτ x j hj W⊆originalChartDomain τ hτ x j:=by
  intro z hz
  have h:=hU ((parameterChart τ hτ x j hj) z) hz.2
  rwa [(parameterChart τ hτ x j hj).left_inv hz.1] at h
lemma sourcePatch_open (W:Set ComplexVectors) (hW:IsOpen W)
    (hU:∀w∈W,(parameterChart τ hτ x j hj).symm w∈originalChartDomain τ hτ x j):
    IsOpen (sourcePatch τ hτ x j hj W):=
  (DiscreteComplexPeriodAtlas318.localChart (P τ) x).isOpen_image_symm_of_subset_target
    ((parameterChart τ hτ x j hj).isOpen_inter_preimage hW)
    (fun z hz=>(parameterDomain_subset τ hτ x j hj W hU hz).1)

/-- Exact full-image localization for the actual graph's original
source patch, expressed in the independently constructed target chart. -/
theorem original_image_chart_patch (W:Set ComplexVectors) (hW:IsOpen W)
    (hU:∀w∈W,(parameterChart τ hτ x j hj).symm w∈originalChartDomain τ hτ x j):
    ∃O:Set (Target 1),IsOpen O ∧
      projectiveMap τ hτ 1 ⁻¹' O=sourcePatch τ hτ x j hj W ∧
      ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j ''
        (Set.range (projectiveMap τ hτ 1)∩O)=
        ratioVector τ hτ 1 j '' parameterDomain τ hτ x j hj W:=by
  obtain ⟨O,hO,hpre,himage⟩:=isolate_source_patch τ hτ
    (sourcePatch τ hτ x j hj W) (sourcePatch_open τ hτ x j hj W hW hU)
  refine ⟨O,hO,hpre,?_⟩
  rw [himage,sourcePatch,Set.image_image,Set.image_image]
  apply Set.image_congr
  intro z _
  exact actual_original_formula τ hτ x j z
end PELOriginalEmbeddedImageNeighborhood318
