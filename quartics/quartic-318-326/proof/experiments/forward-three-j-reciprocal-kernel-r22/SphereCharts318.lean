module
public import SphereInversion318
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public section
noncomputable section
open Function Filter Topology TopologicalSpace
open scoped OnePoint Manifold ContDiff
namespace SphereCharts318
open SphereInversion318
set_option maxHeartbeats 0

/-- The independently given finite chart of the standard complex sphere. -/
@[expose] def finiteChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  (OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph ((↑) : ℂ → OnePoint ℂ)).symm

/-- The independently given reciprocal chart, using the proved sphere inversion. -/
@[expose] def infinityChart : OpenPartialHomeomorph (OnePoint ℂ) ℂ :=
  inversionHomeomorph.toOpenPartialHomeomorph.trans finiteChart

lemma finite_source : finiteChart.source=Set.range ((↑) : ℂ → OnePoint ℂ) := by
  simp only [finiteChart,OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]

lemma finite_target : finiteChart.target=Set.univ := by
  simp only [finiteChart,OpenPartialHomeomorph.symm_target,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source]

lemma finite_apply (t : ℂ) : finiteChart (t : OnePoint ℂ)=t :=
  Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv ..

lemma finite_symm_apply (t : ℂ) : finiteChart.symm t=(t : OnePoint ℂ) := rfl

lemma infinity_source_iff (z : OnePoint ℂ) :
    z ∈ infinityChart.source ↔ inversion z ∈ Set.range ((↑) : ℂ → OnePoint ℂ) := by
  simp only [infinityChart,OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source,Set.mem_inter_iff,Set.mem_univ,true_and,
    Set.mem_preimage,finite_source]
  rfl

lemma infinity_center : (OnePoint.infty : OnePoint ℂ) ∈ infinityChart.source := by
  rw [infinity_source_iff,inversion_infty]
  exact Set.mem_range_self (0:ℂ)

lemma finite_center {z : OnePoint ℂ} (hz : z ≠ (OnePoint.infty : OnePoint ℂ)) : z ∈ finiteChart.source := by
  rw [finite_source]
  exact not_not.mp (fun h => hz (OnePoint.notMem_range_coe_iff.mp h))

@[expose] def chosenChart (z : OnePoint ℂ) : OpenPartialHomeomorph (OnePoint ℂ) ℂ := by
  classical
  exact if z=(OnePoint.infty : OnePoint ℂ) then infinityChart else finiteChart

@[expose,instance_reducible] def sphereChartedSpace : ChartedSpace ℂ (OnePoint ℂ) where
  atlas := {finiteChart,infinityChart}
  chartAt := chosenChart
  mem_chart_source z := by
    classical
    unfold chosenChart
    split_ifs with hz
    · simpa only [hz] using infinity_center
    · exact finite_center hz
  chart_mem_atlas z := by
    classical
    unfold chosenChart
    split_ifs <;> simp

end SphereCharts318
