module
public import SphereComplexCurve318
public import ActualThreeFilledHolomorphic318
public section
noncomputable section
open Function Filter Topology TopologicalSpace
open scoped Manifold ContDiff
namespace ActualThreeComplexAtlas318
open SphereCharts318 SphereComplexCurve318
open ActualThreeCuspFilling318 ActualThreeFilledParameter318 ActualThreeFilledHolomorphic318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Pull the independent standard sphere charts back along the already proved
original compact map. The separately proved original/cusp germ comparisons
identify these coordinates with the independently defined source holomorphy. -/
@[expose] def sourceChart (e : OpenPartialHomeomorph (OnePoint ℂ) ℂ) :
    OpenPartialHomeomorph Filled ℂ :=
  e.lift_openEmbedding compactHomeomorph.symm.isOpenEmbedding

lemma sourceChart_apply (e : OpenPartialHomeomorph (OnePoint ℂ) ℂ) (z : Filled) :
    sourceChart e z=e (compactHomeomorph z) := by
  calc
    sourceChart e z = sourceChart e (compactHomeomorph.symm (compactHomeomorph z)) :=
      congrArg (sourceChart e) (compactHomeomorph.symm_apply_apply z).symm
    _ = e (compactHomeomorph z) := e.lift_openEmbedding_apply _

@[expose,instance_reducible] def filledChartedSpace : ChartedSpace ℂ Filled where
  atlas := sourceChart '' {finiteChart,infinityChart}
  chartAt z := sourceChart (chosenChart (compactHomeomorph z))
  mem_chart_source z := by
    let := sphereChartedSpace
    exact ⟨compactHomeomorph z,mem_chart_source ℂ (compactHomeomorph z),
      compactHomeomorph.symm_apply_apply z⟩
  chart_mem_atlas z := by
    let := sphereChartedSpace
    exact ⟨chosenChart (compactHomeomorph z),chart_mem_atlas ℂ (compactHomeomorph z),rfl⟩

/-- Actual transition maps are the same independent sphere transitions; the
original compact map cancels exactly, with no new topology on the source. -/
lemma source_transition (e e' : OpenPartialHomeomorph (OnePoint ℂ) ℂ) :
    (sourceChart e).symm.trans (sourceChart e')=e.symm.trans e' :=
  OpenPartialHomeomorph.lift_openEmbedding_trans e e' compactHomeomorph.symm.isOpenEmbedding

theorem filled_isManifold :
    let := filledChartedSpace
    IsManifold 𝓘(ℂ) ω Filled := by
  let := filledChartedSpace
  let := sphereChartedSpace
  let := sphere_isManifold
  refine { compatible:=?_ }
  intro a a' ha ha'
  obtain ⟨e,he,rfl⟩ := ha
  obtain ⟨e',he',rfl⟩ := ha'
  rw [source_transition]
  exact (contDiffGroupoid ω 𝓘(ℂ)).compatible he he'

/-- The original compact filling, with its unchanged topology, now carries
an actual complex analytic manifold structure. Its canonical source-germ
identification is the explicit original/cusp comparison proved separately. -/
theorem actual_compact_complex_curve :
    let := filledChartedSpace
    IsManifold 𝓘(ℂ) ω Filled ∧ CompactSpace Filled ∧ T2Space Filled ∧
      SecondCountableTopology Filled := by
  let := filledChartedSpace
  exact ⟨filled_isManifold,ActualThreeCuspCompact318.filled_compactSpace,
    ActualThreeCuspHausdorff318.filled_t2,ActualThreeCuspFilling318.filled_secondCountable⟩

end ActualThreeComplexAtlas318
