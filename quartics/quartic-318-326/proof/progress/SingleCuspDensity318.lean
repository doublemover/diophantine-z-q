module
public import ActualSingleCusp318
public import Mathlib.Topology.Algebra.Module.PerfectSpace
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318
open PeterssonQuotient318 ActualSingleCusp318
namespace SingleCuspDensity318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem punctured_dense : Dense {q:disc | q.val≠0} :=
  (dense_compl_singleton (0:ℂ)).preimage disc.isOpen.isOpenEmbedding_subtypeVal.isOpenMap

/-- The original actual quotient is dense in its genuine one-cusp attachment. -/
theorem original_dense (N:ℕ) : DenseRange (original N) := by
  intro z
  rcases TwoChartGluing318.jointly_surjective (overlap N) z with ⟨b,rfl⟩ | ⟨q,rfl⟩
  · exact subset_closure ⟨b,rfl⟩
  · have hc : cuspChart N q∈closure (cuspChart N '' {q:disc | q.val≠0}) :=
      mem_closure_image (cuspChart_isOpenEmbedding N).continuous.continuousAt (punctured_dense q)
    apply closure_mono _ hc
    rintro z ⟨q,hq,rfl⟩
    rw [range_original]
    intro he
    have hzero : q=zeroPoint := (cuspChart_isOpenEmbedding N).injective he
    exact hq (congrArg Subtype.val hzero)

end SingleCuspDensity318
