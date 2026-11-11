module
public import ActualOriginalPositiveQuadricChart318
public section
noncomputable section
namespace ActualOriginalArchimedeanChartInput318
open QuadricCRTAssembly318 ActualOriginalPositiveRealPoint318 ActualOriginalRealGoodRegion318
open ActualOriginalSmoothWeight318 ActualOriginalPositiveQuadricChart318 Filter
open scoped Topology ContDiff
set_option maxHeartbeats 16000000

@[expose] def graphDensity (κ : ℝ) (W : Coordinates ℝ→ℝ) (v : Parameters) : ℝ :=
  W (graph κ v)/(2*Real.sqrt (radicand κ v))
lemma graphDensity_continuousAt (κ : ℝ) (W : Coordinates ℝ→ℝ)
    (hW : Continuous W) (v : Parameters) (hv : 0<radicand κ v) :
    ContinuousAt (graphDensity κ W) v := by
  unfold graphDensity
  exact (hW.comp (graph_continuous κ)).continuousAt.div
    (continuous_const.mul (Real.continuous_sqrt.comp (radicand_continuous κ))).continuousAt
    (mul_ne_zero (by norm_num) (ne_of_gt (Real.sqrt_pos.2 hv)))
lemma graphDensity_at_original_point (κ : ℝ) (W : Coordinates ℝ→ℝ)
    (x : Coordinates ℝ) (hQ : equation κ x=0) (ha : 0<x.1.1) (hWx : W x=1) :
    graphDensity κ W (projection x)=1/(2*x.1.1) := by
  unfold graphDensity
  rw [graph_projection κ x hQ ha.le,hWx,original_radicand κ x hQ,Real.sqrt_sq ha.le]

/-- The same produced compact smooth ambient weight has a genuine
positive continuous density on an actual neighborhood of its original
quadric point, with the exact original normal derivative denominator.
This is a chart input, NOT an assertion about an oscillatory singular
integral or the global circle-method asymptotic. -/
theorem actual_original_archimedean_chart_input {J : Type*} [Fintype J]
    (κ : ℝ) (hκ : 0<κ) (γ : J→ℝ) :
    ∃(x : Coordinates ℝ) (W : Coordinates ℝ→ℝ) (η : ℝ),
      equation κ x=0 ∧ 0<x.1.1 ∧ 0<η ∧ HasCompactSupport W ∧
      ContDiff ℝ ∞ W ∧ (∀y,0≤W y ∧ W y≤1) ∧ W x=1 ∧
      (∀y∈tsupport W, y∈region γ ∧ η<ActualQuadricTaylor318.gradient κ y 0) ∧
      graph κ (projection x)=x ∧
      graphDensity κ W (projection x)=1/(2*x.1.1) ∧
      ∀ᶠv in 𝓝 (projection x),0<radicand κ v ∧ 0<graphDensity κ W v := by
  obtain ⟨x,W,η,hQ,hη,hWc,hWd,hWb,hWx,hWs⟩ := actual_original_smooth_weight κ hκ γ
  have hxn : x∈Function.support W := by
    change W x≠0
    rw [hWx]
    norm_num
  have hxt : x∈tsupport W := subset_closure hxn
  have ha : 0<x.1.1 := (hWs x hxt).1.1
  have hr : 0<radicand κ (projection x) := by
    rw [original_radicand κ x hQ]
    exact sq_pos_of_pos ha
  have hd := graphDensity_at_original_point κ W x hQ ha hWx
  have hp : 0<graphDensity κ W (projection x) := by rw [hd];positivity
  have hevR : ∀ᶠv in 𝓝 (projection x),0<radicand κ v :=
    (radicand_continuous κ).continuousAt.eventually (eventually_gt_nhds hr)
  have hevD : ∀ᶠv in 𝓝 (projection x),0<graphDensity κ W v :=
    (graphDensity_continuousAt κ W hWd.continuous (projection x) hr).eventually
      (eventually_gt_nhds hp)
  exact ⟨x,W,η,hQ,ha,hη,hWc,hWd,hWb,hWx,hWs,
    graph_projection κ x hQ ha.le,hd,hevR.and hevD⟩

end ActualOriginalArchimedeanChartInput318
