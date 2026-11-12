module
public import PELOriginalEmbeddedImageNeighborhood318
public import PELOriginalHyperplanePullbackHolomorphy318
public section
noncomputable section
namespace PELOriginalLevelThreeAnalyticEmbedding318
open QuaternionicRealPeriod318 PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalAllLevelHolomorphicMap318 PELOriginalLevelThreeLocalImage318
open PELOriginalPolarizationTransitions318 PELOriginalAllLevelProjectiveMap318
open DiscreteComplexPeriodAtlas318 ComplexProjectiveQuotientTopology318 Set Topology
open PELOriginalLevelThreeAmbientImage318 PELOriginalEmbeddedImageNeighborhood318
open SplitHolomorphicImage318 SplitHolomorphicGraphCoordinates318
variable (τ:ℂ) (hτ:0<τ.im)
local instance discretePeriods:DiscreteTopology (P τ):=
  PELOriginalPeriodLattice318.original_discrete τ hτ
local instance targetTopology:TopologicalSpace (Target 1):=topology (Label 3)

/-- The WHOLE actual closed projective image, in an actual ambient
neighborhood of each original point, is a holomorphic zero-normal slice.
The original global embedding is used to exclude distant source points. -/
theorem whole_image_local_slice (x:ComplexVectors) (j:Label 3)
    (hj:value τ hτ 3 j x≠0):
    ∃W:Set ComplexVectors,IsOpen W ∧
    ∃O:Set (Target 1),IsOpen O ∧ projectiveMap τ hτ 1 (DiscreteComplexPeriodAtlas318.projection (P τ) x)∈O ∧
    ∃e:OpenPartialHomeomorph (TargetModel 1)
      (ComplexVectors×Normal (fderiv ℂ (ratioVector τ hτ 1 j) x)),
      e.target=Prod.fst ⁻¹' W ∧ DifferentiableOn ℂ e e.source ∧
      DifferentiableOn ℂ e.symm e.target ∧
      Set.range (projectiveMap τ hτ 1)∩O⊆
        (ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j).source ∧
      ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j ''
        (Set.range (projectiveMap τ hτ 1)∩O)⊆e.source ∧
      e '' (ComplexProjectiveComplexAtlas318.localChart (Label 3) 0 j ''
        (Set.range (projectiveMap τ hτ 1)∩O))=
        {q|q.1∈W ∧ q.2=0}:=by
  obtain ⟨W,hW,hWx,e,hes,het,he,hei,hU,hflat⟩:=actual_ambient_chart τ hτ x j hj
  obtain ⟨O,hO,hpre,himage⟩:=original_image_chart_patch τ hτ x j hj W hW hU
  have hcenter:projectiveMap τ hτ 1 (DiscreteComplexPeriodAtlas318.projection (P τ) x)∈O:=by
    change DiscreteComplexPeriodAtlas318.projection (P τ) x∈projectiveMap τ hτ 1 ⁻¹' O
    rw [hpre]
    refine ⟨x,⟨parameterChart_center τ hτ x j hj,?_⟩,?_⟩
    · exact hWx
    · exact DiscreteComplexPeriodAtlas318.localChart_symm (P τ) x x
  refine ⟨W,hW,O,hO,hcenter,e,het,he,hei,?_,?_,?_⟩
  · intro p hp
    obtain ⟨q,hq⟩:=hp.1
    have hqO:projectiveMap τ hτ 1 q∈O:=hq.symm ▸ hp.2
    have hqU:q∈sourcePatch τ hτ x j hj W:=by
      rw [←hpre]
      exact hqO
    obtain ⟨z,hz,hzq⟩:=hqU
    have hzU:=parameterDomain_subset τ hτ x j hj W hU hz
    rw [←hq,←hzq,DiscreteComplexPeriodAtlas318.localChart_symm,original_covering_square]
    exact (mk_mem_domain (Label 3) j _ _).mpr hzU.2
  · intro y hy
    rw [himage] at hy
    obtain ⟨z,hz,rfl⟩:=hy
    rw [hes]
    exact hz.2
  · rw [himage]
    exact hflat

/-- The polarization identification is with the SAME original line
bundle: the hyperplane line on the actual embedded image pulls back to
its THIRD power, with the already constructed local biholomorphic fiber
comparison. Neither an algebraic line nor rational descent is inferred. -/
@[expose] def hyperplane_pullback:
    PELOriginalPolarizationPowerBundle318.PowerTotal τ hτ 3≃ₜ
      PELOriginalHyperplanePullback318.PullbackTotal τ hτ 1:=
  PELOriginalHyperplanePullbackTopology318.homeomorph τ hτ 1
lemma hyperplane_over_original_base
    (p:PELOriginalPolarizationPowerBundle318.PowerTotal τ hτ 3):
    (hyperplane_pullback τ hτ p).1=p.1:=rfl
lemma hyperplane_original_chart(a:ComplexVectors)(q:Base τ)
    (ha:q∈baseSet τ hτ a)(j:Label 3)
    (hj:q∈(PELOriginalHyperplanePullback318.pullbackCore τ hτ 1).baseSet j)
    (v:PELOriginalPolarizationPowerBundle318.PowerFiber τ hτ 3 q):
    ((PELOriginalHyperplanePullback318.pullbackCore τ hτ 1).localTriv j
      ⟨q,PELOriginalHyperplanePullback318.fiberEquivalence τ hτ 1 q v⟩).2=
      ((PELOriginalPolarizationPowerBundle318.powerCore τ hτ 3).localTriv a ⟨q,v⟩).2/
        ((PELOriginalPolarizationPowerBundle318.powerCore τ hτ 3).localTriv a
          (levelSection τ hτ 3 j q)).2:=
  PELOriginalHyperplanePullback318.original_chart_ratio τ hτ 1 a q ha j hj v
end PELOriginalLevelThreeAnalyticEmbedding318
