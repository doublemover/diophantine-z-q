module
public import PELOriginalOrderedCompletedChartSquares318
public section
noncomputable section
namespace PELOriginalOrderedCompletedContinuity318
open PELOriginalCommonContactBase318 PELOriginalOrderedCharacterCoordinate318
open FourRootNormalizedPointCharts318 PELOriginalOrderedCompletedChartSquares318
local instance : TopologicalSpace (Completed branches):=FourRootGluedTopology318.topology branches

lemma finite_continuous (i:Fin 4):Continuous (completedMap i ∘ finiteChart branches):=by
  have he:completedMap i ∘ finiteChart branches=
      LegendrePlaneOverlap318.finiteChart (parameter i) ∘
        PELOriginalOrderedFiniteAnalyticCoordinates318.finiteMap i:=funext (finite_square i)
  rw [he]
  exact (LegendrePlaneOverlap318.finite_open _).continuous.comp
    (PELOriginalOrderedFiniteAnalyticCoordinates318.continuous_finiteMap i)
lemma infinity_neighborhood_continuous (i:Fin 4):Continuous
    (fun p:PELOriginalOrderedInfinityAnalyticCoordinates318.N i=>
      completedMap i (infinityChart branches p.val)):=by
  have he:(fun p:PELOriginalOrderedInfinityAnalyticCoordinates318.N i=>
      completedMap i (infinityChart branches p.val))=
      LegendrePlaneOverlap318.infinityChart (parameter i) ∘
        PELOriginalOrderedInfinityAnalyticCoordinates318.infinityMap i:=funext (infinity_square i)
  rw [he]
  exact (LegendrePlaneOverlap318.infinity_open _).continuous.comp
    (PELOriginalOrderedInfinityAnalyticCoordinates318.continuous_infinityMap i)
lemma infinity_overlap_continuous (i:Fin 4):Continuous
    (fun p:InfinityOverlap branches=>completedMap i (infinityChart branches p.val)):=by
  have he:(fun p:InfinityOverlap branches=>completedMap i (infinityChart branches p.val))=
      (completedMap i ∘ finiteChart branches) ∘
        (fun p:InfinityOverlap branches=>(toFinite branches p).val):=by
    funext p
    rw [infinityChart_nonzero branches p.val p.property]
    rfl
  rw [he]
  exact (finite_continuous i).comp
    (continuous_subtype_val.comp (FourRootNormalizedOverlap318.toFinite_continuous branches))

/-- Two ACTUAL open neighborhoods cover the old infinity chart: u is
nonzero, or the three-ratio denominator is nonzero. The second contains
all eight original infinity signs and has no inverse of u. -/
lemma infinity_continuous (i:Fin 4):Continuous (completedMap i ∘ infinityChart branches):=by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp:p.val.1=0
  · have hn:=FourRootInfinityEvaluationNeighborhood318.contains_zero branches
      (PELOriginalCharacterInfinityMaps318.indices i) p hp
    exact ((FourRootInfinityEvaluationNeighborhood318.neighborhood_open branches
      (PELOriginalCharacterInfinityMaps318.indices i)).isOpenEmbedding_subtypeVal.continuousAt_iff).mp
        ((infinity_neighborhood_continuous i).continuousAt (x:=⟨p,hn⟩))
  · exact ((FourRootNormalizedOverlap318.infinity_overlap_open branches).
      isOpenEmbedding_subtypeVal.continuousAt_iff).mp
        ((infinity_overlap_continuous i).continuousAt (x:=⟨p,hp⟩))

/-- Continuity in the independently glued affine/infinity source and
target topologies, for the exact Scheme-induced completed point map. -/
theorem continuous (i:Fin 4):Continuous (completedMap i):=
  (FourRootGluedTopology318.continuous_iff branches _).mpr
    ⟨finite_continuous i,infinity_continuous i⟩
end PELOriginalOrderedCompletedContinuity318
