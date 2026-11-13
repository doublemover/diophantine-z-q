module
public import ActualOriginalAbelSingularIntegral318
public section
noncomputable section
namespace ActualOriginalSmoothLevelDensity318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318
open ActualOriginalNormalLevelChart318 ActualOriginalJointLevelDensity318
open Filter
open scoped Topology ContDiff
set_option maxHeartbeats 16000000

lemma levelRadicand_contDiff (κ : ℝ) : ContDiff ℝ ∞ (levelRadicand κ) := by
  unfold levelRadicand radicand
  fun_prop

lemma levelGraph_contDiffAt (κ : ℝ) (z : LevelParameters)
    (hz : levelRadicand κ z ≠ 0) : ContDiffAt ℝ ∞ (levelGraph κ) z := by
  have hs := (levelRadicand_contDiff κ).contDiffAt.sqrt hz
  unfold levelGraph
  exact (hs.prodMk (contDiffAt_snd.fst)).prodMk
    ((contDiffAt_snd.snd.fst).prodMk (contDiffAt_snd.snd.snd))

/-- At every point whose original graph lies outside the ORIGINAL weight
support, the actual density vanishes on a whole neighborhood. This also
handles the singular square-root locus without differentiating sqrt there. -/
lemma levelDensity_eventually_zero (κ : ℝ) (W : Coordinates ℝ → ℝ)
    (z : LevelParameters) (hz : levelGraph κ z ∉ tsupport W) :
    levelDensity κ W =ᶠ[𝓝 z] 0 := by
  have hw : W =ᶠ[𝓝 (levelGraph κ z)] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp hz
  have hc := hw.comp_tendsto (levelGraph_continuous κ).continuousAt
  filter_upwards [hc] with y hy
  change W (levelGraph κ y) / (2 * Real.sqrt (levelRadicand κ y)) = 0
  rw [show W (levelGraph κ y) = 0 from hy, zero_div]

/-- The exact original normal-coordinate density is smooth everywhere.
On its original support the positive original gradient keeps the square
root and the Jacobian denominator away from zero. Outside that support the
actual density is locally zero, including at the square-root branch locus. -/
theorem actual_level_density_smooth (κ η : ℝ) (hη : 0 < η)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (hb : ∀ x ∈ tsupport W, η < ActualQuadricTaylor318.gradient κ x 0) :
    ContDiff ℝ ∞ (levelDensity κ W) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : levelGraph κ z ∈ tsupport W
  · have hg := hb (levelGraph κ z) hz
    change η < 2 * Real.sqrt (levelRadicand κ z) at hg
    have hs : 0 < Real.sqrt (levelRadicand κ z) := by linarith
    have hr : levelRadicand κ z ≠ 0 := ne_of_gt (Real.sqrt_pos.mp hs)
    have hgraph := levelGraph_contDiffAt κ z hr
    have hroot := (levelRadicand_contDiff κ).contDiffAt.sqrt hr
    exact (hW.contDiffAt.comp z hgraph).div (contDiffAt_const.mul hroot)
      (ne_of_gt (mul_pos (by norm_num) hs))
  · exact contDiffAt_const.congr_of_eventuallyEq
      (levelDensity_eventually_zero κ W z hz)

end ActualOriginalSmoothLevelDensity318
