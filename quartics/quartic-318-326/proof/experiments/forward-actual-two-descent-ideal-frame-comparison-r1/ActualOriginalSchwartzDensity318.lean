module
public import ActualOriginalSmoothLevelDensity318
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public section
noncomputable section
namespace ActualOriginalSchwartzDensity318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318
open ActualOriginalNormalLevelChart318 ActualOriginalJointLevelDensity318
open ActualOriginalSmoothLevelDensity318
open scoped ContDiff
set_option maxHeartbeats 16000000

/-- The literal original joint level density as a Schwartz function.
Its coercion is definitionally the density previously used for the original
ambient Fourier identity, not a substitute profile or independent weight. -/
@[expose] def actualLevelSchwartz (κ η : ℝ) (hη : 0 < η)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (hb : ∀ x ∈ tsupport W, η < ActualQuadricTaylor318.gradient κ x 0) :
    SchwartzMap LevelParameters ℝ :=
  (level_density_compact κ η hη W hWc hb).toSchwartzMap
    (actual_level_density_smooth κ η hη W hW hb)

theorem actual_level_schwartz_apply (κ η : ℝ) (hη : 0 < η)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (hb : ∀ x ∈ tsupport W, η < ActualQuadricTaylor318.gradient κ x 0)
    (z : LevelParameters) :
    actualLevelSchwartz κ η hη W hW hWc hb z = levelDensity κ W z := rfl

/-- Actual compact support and smoothness, before any Fourier-decay or
Poisson claim. Both facts concern the very same joint density. -/
theorem actual_level_density_compact_smooth (κ η : ℝ) (hη : 0 < η)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (hb : ∀ x ∈ tsupport W, η < ActualQuadricTaylor318.gradient κ x 0) :
    HasCompactSupport (levelDensity κ W) ∧ ContDiff ℝ ∞ (levelDensity κ W) :=
  ⟨level_density_compact κ η hη W hWc hb,
    actual_level_density_smooth κ η hη W hW hb⟩

end ActualOriginalSchwartzDensity318
