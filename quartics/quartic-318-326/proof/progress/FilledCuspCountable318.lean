module
public import FilledCuspHausdorff318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318
open PeterssonQuotient318 ActualSingleCusp318
namespace FilledCuspCountable318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- The actual gluing inherits second countability from its two actual open
pieces via their continuous open jointly-surjective sum map. -/
theorem filled_secondCountable (N:ℕ) : SecondCountableTopology (Filled N) := by
  letI:SecondCountableTopology (Base (image N)) :=
    ContinuousConstSMul.secondCountableTopology
  let f : Base (image N) ⊕ disc → Filled N := Sum.elim (original N) (cuspChart N)
  have hc:Continuous f := continuous_sum_dom.mpr
    ⟨(original_isOpenEmbedding N).continuous,(cuspChart_isOpenEmbedding N).continuous⟩
  have ho:IsOpenMap f := (original_isOpenEmbedding N).isOpenMap.sumElim
    (cuspChart_isOpenEmbedding N).isOpenMap
  have hs:Function.Surjective f := by
    intro z
    rcases TwoChartGluing318.jointly_surjective (overlap N) z with ⟨b,hb⟩ | ⟨q,hq⟩
    · exact ⟨Sum.inl b,hb⟩
    · exact ⟨Sum.inr q,hq⟩
  exact (show IsOpenQuotientMap f from ⟨hs,hc,ho⟩).secondCountableTopology

end FilledCuspCountable318
