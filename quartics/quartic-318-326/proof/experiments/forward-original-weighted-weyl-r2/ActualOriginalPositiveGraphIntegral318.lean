module
public import ActualOriginalGraphDensityRegularity318
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public section
noncomputable section
namespace ActualOriginalPositiveGraphIntegral318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318 ActualOriginalArchimedeanChartInput318
open ActualOriginalGraphDensityRegularity318 MeasureTheory Filter
open ActualOriginalRealGoodRegion318
open scoped Topology ContDiff
set_option maxHeartbeats 16000000

@[expose] def graphMass (κ : ℝ) (W : Coordinates ℝ→ℝ) : ℝ :=
  ∫v : Parameters,graphDensity κ W v

lemma actual_density_integrable (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ)
    (hW : Continuous W) (hWc : HasCompactSupport W)
    (hb : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0) :
    Integrable (graphDensity κ W) :=
  (actual_density_continuous κ η hη W hW hb).integrable_of_hasCompactSupport
    (actual_density_compact κ W hWc)

lemma actual_mass_positive (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ)
    (hW : Continuous W) (hWc : HasCompactSupport W) (hWn : ∀x,0≤W x)
    (hb : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0)
    (x : Coordinates ℝ) (hQ : equation κ x=0) (ha : 0<x.1.1) (hWx : W x=1) :
    0<graphMass κ W := by
  have hint := actual_density_integrable κ η hη W hW hWc hb
  apply (integral_pos_iff_support_of_nonneg (actual_density_nonneg κ W hWn) hint).mpr
  have hp : 0<graphDensity κ W (projection x) := by
    rw [graphDensity_at_original_point κ W x hQ ha hWx]
    positivity
  have he : ∀ᶠv in 𝓝 (projection x),0<graphDensity κ W v :=
    (actual_density_continuous κ η hη W hW hb).continuousAt.eventually (eventually_gt_nhds hp)
  apply measure_pos_of_mem_nhds volume
  filter_upwards [he] with v hv
  exact ne_of_gt hv

/-- The same genuinely produced weight has a finite, strictly positive
integral over the ORIGINAL graph with the exact 1/(2a) factor and ordinary
product Lebesgue volume in the ORIGINAL (b,c,d,w) coordinates. -/
theorem actual_original_positive_graph_integral {J : Type*} [Fintype J]
    (κ : ℝ) (hκ : 0<κ) (γ : J→ℝ) :
    ∃(x : Coordinates ℝ) (W : Coordinates ℝ→ℝ) (η : ℝ),
      equation κ x=0 ∧ 0<x.1.1 ∧ 0<η ∧ HasCompactSupport W ∧
      ContDiff ℝ ∞ W ∧ (∀y,0≤W y ∧ W y≤1) ∧ W x=1 ∧
      (∀y∈tsupport W,y∈region γ ∧ η<ActualQuadricTaylor318.gradient κ y 0) ∧
      Integrable (graphDensity κ W) ∧ 0<graphMass κ W := by
  obtain ⟨x,W,η,hQ,ha,hη,hWc,hWd,hWb,hWx,hWs,hgraph,hvalue,hneigh⟩ :=
    actual_original_archimedean_chart_input κ hκ γ
  have hb : ∀y∈tsupport W,η<ActualQuadricTaylor318.gradient κ y 0 := fun y hy => (hWs y hy).2
  exact ⟨x,W,η,hQ,ha,hη,hWc,hWd,hWb,hWx,hWs,
    actual_density_integrable κ η hη W hWd.continuous hWc hb,
    actual_mass_positive κ η hη W hWd.continuous hWc (fun y => (hWb y).1) hb x hQ ha hWx⟩

end ActualOriginalPositiveGraphIntegral318
