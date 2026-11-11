module
public import ActualGraphCompactSupport318
public section
noncomputable section
namespace ActualOriginalGraphDensityRegularity318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318 ActualGraphCompactSupport318
open ActualOriginalArchimedeanChartInput318
set_option maxHeartbeats 16000000

@[expose] def safeDensity (κ η : ℝ) (W : Coordinates ℝ→ℝ) (v : Parameters) : ℝ :=
  W (graph κ v)/max η (2*Real.sqrt (radicand κ v))
lemma safeDensity_continuous (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ)
    (hW : Continuous W) : Continuous (safeDensity κ η W) := by
  unfold safeDensity
  refine (hW.comp (graph_continuous κ)).div
    (continuous_const.max (continuous_const.mul (Real.continuous_sqrt.comp (radicand_continuous κ)))) ?_
  intro v
  exact ne_of_gt (lt_of_lt_of_le hη (le_max_left _ _))

/-- The denominator regularization does not change the ORIGINAL density
anywhere: where the numerator is nonzero, the produced support bound makes
the maximum equal the exact original derivative. -/
lemma actual_safe_density_eq (κ η : ℝ) (W : Coordinates ℝ→ℝ)
    (hbound : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0) :
    safeDensity κ η W=graphDensity κ W := by
  funext v
  by_cases h : W (graph κ v)=0
  · simp only [safeDensity,graphDensity,h,zero_div]
  · have hx : graph κ v∈tsupport W := subset_closure h
    have hb := hbound (graph κ v) hx
    change η<2*Real.sqrt (radicand κ v) at hb
    simp only [safeDensity,graphDensity,max_eq_right hb.le]

lemma actual_density_compact (κ : ℝ) (W : Coordinates ℝ→ℝ)
    (hW : HasCompactSupport W) : HasCompactSupport (graphDensity κ W) := by
  apply (actual_graph_compact_support κ W hW).mono
  intro v hv
  change W (graph κ v)≠0
  intro hh
  apply hv
  simp only [graphDensity,hh,zero_div]
lemma actual_density_continuous (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ)
    (hW : Continuous W)
    (hbound : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0) :
    Continuous (graphDensity κ W) := by
  rw [←actual_safe_density_eq κ η W hbound]
  exact safeDensity_continuous κ η hη W hW
lemma actual_density_nonneg (κ : ℝ) (W : Coordinates ℝ→ℝ) (hW : ∀x,0≤W x) :
    ∀v,0≤graphDensity κ W v := by
  intro v
  exact div_nonneg (hW _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

end ActualOriginalGraphDensityRegularity318
