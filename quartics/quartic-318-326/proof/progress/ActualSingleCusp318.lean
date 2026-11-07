module
public import TwoChartGluing318
public import BiholomorphicCusp318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology TopologicalSpace GammaOneFiber318 GammaOneAtlas318
open PeterssonQuotient318 HighQParameter318 ActualCuspHomeomorph318
namespace ActualSingleCusp318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def disc : Opens ℂ := ⟨{q | ‖q‖<radius height},isOpen_lt continuous_norm continuous_const⟩
@[expose] def zeroPoint : disc := ⟨0,by change ‖(0:ℂ)‖<radius height; simpa using radius_positive height⟩

instance disc_nonempty : Nonempty disc := ⟨zeroPoint⟩

/-- The genuine overlap identifies the existing quotient cusp neighborhood
with the punctured part of the actual filled disc. -/
@[expose] def overlap (N:ℕ) : OpenPartialHomeomorph (Base (image N)) disc :=
  ((ActualCuspPartialChart318.chart N).symm.subtypeRestr disc_nonempty).symm

theorem overlap_target (N:ℕ) : (overlap N).target={q:disc | q.val≠0} := by
  ext q
  simp only [overlap,OpenPartialHomeomorph.symm_target,OpenPartialHomeomorph.subtypeRestr_source,
    OpenPartialHomeomorph.symm_source,ActualCuspPartialChart318.chart_target,Set.mem_preimage,
    punctured,Set.mem_ofPred_eq]
  exact and_iff_left q.property

theorem overlap_source (N:ℕ) : (overlap N).source=neighborhood N height := by
  apply Set.Subset.antisymm
  · exact (ActualCuspPartialChart318.chart N).symm.subtypeRestr_target_subset disc_nonempty
  · intro b hb
    have hq:ActualCuspPartialChart318.chart N b∈punctured height :=
      (ActualCuspPartialChart318.chart N).map_source hb
    have hm := (ActualCuspPartialChart318.chart N).symm.map_subtype_source disc_nonempty
      (x:=⟨ActualCuspPartialChart318.chart N b,hq.2⟩) hq
    simpa only [overlap,OpenPartialHomeomorph.symm_source,(ActualCuspPartialChart318.chart N).left_inv hb] using hm

/-- Actual gluing of the original quotient and one filled cusp disc. -/
abbrev Filled (N:ℕ) := TwoChartGluing318.Space (overlap N)

@[expose] def original (N:ℕ) : Base (image N)→Filled N := TwoChartGluing318.left (overlap N)
@[expose] def cuspChart (N:ℕ) : disc→Filled N := TwoChartGluing318.right (overlap N)
@[expose] def cusp (N:ℕ) : Filled N := cuspChart N zeroPoint

theorem original_isOpenEmbedding (N:ℕ) : IsOpenEmbedding (original N) :=
  TwoChartGluing318.left_isOpenEmbedding (overlap N)

theorem cuspChart_isOpenEmbedding (N:ℕ) : IsOpenEmbedding (cuspChart N) :=
  TwoChartGluing318.right_isOpenEmbedding (overlap N)

theorem original_ne_cusp (N:ℕ) (b:Base (image N)) : original N b≠cusp N := by
  intro he
  obtain ⟨hb,hq⟩:= (TwoChartGluing318.left_eq_right_iff (overlap N) b zeroPoint).mp he
  have htarget := (overlap N).map_source hb
  rw [hq,overlap_target] at htarget
  exact htarget rfl

/-- Exactly one point has been added. This is a theorem about the actual
TopCat gluing, not a chosen set-equivalence called a compactification. -/
theorem range_original (N:ℕ) : Set.range (original N)={z | z≠cusp N} := by
  ext z
  constructor
  · rintro ⟨b,rfl⟩
    exact original_ne_cusp N b
  · intro hz
    rcases TwoChartGluing318.jointly_surjective (overlap N) z with ⟨b,hb⟩ | ⟨q,rfl⟩
    · exact ⟨b,hb⟩
    · have hq:q.val≠0 := by
        intro hzero
        have hq0:q=zeroPoint := Subtype.ext hzero
        exact hz (congrArg (cuspChart N) hq0)
      have hqt:q∈(overlap N).target := by rwa [overlap_target]
      refine ⟨(overlap N).symm q,?_⟩
      exact (TwoChartGluing318.left_eq_right_iff _ _ _).mpr
        ⟨(overlap N).map_target hqt,(overlap N).right_inv hqt⟩

/-- The chart is an actual open disc neighborhood of the new cusp. -/
theorem cusp_in_open_disc (N:ℕ) :
    IsOpen (Set.range (cuspChart N)) ∧ cusp N∈Set.range (cuspChart N) :=
  ⟨(cuspChart_isOpenEmbedding N).isOpen_range,⟨zeroPoint,rfl⟩⟩

end ActualSingleCusp318
