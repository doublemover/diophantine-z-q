module
public import ActualOriginalNormalLevelChart318
public section
noncomputable section
namespace ActualOriginalJointLevelDensity318
open QuadricCRTAssembly318 ActualOriginalNormalLevelChart318 ActualOriginalPositiveQuadricChart318
open ActualOriginalArchimedeanChartInput318
set_option maxHeartbeats 16000000

@[expose] def levelDensity (κ : ℝ) (W : Coordinates ℝ→ℝ) (z : LevelParameters) : ℝ :=
  W (levelGraph κ z)/(2*Real.sqrt (levelRadicand κ z))
lemma level_density_zero (κ : ℝ) (W : Coordinates ℝ→ℝ) (v : Parameters) :
    levelDensity κ W (0,v)=graphDensity κ W v := by
  simp only [levelDensity,level_zero_graph,levelRadicand,add_zero,graphDensity]
lemma level_density_nonneg (κ : ℝ) (W : Coordinates ℝ→ℝ) (hW : ∀x,0≤W x) :
    ∀z,0≤levelDensity κ W z := fun z =>
  div_nonneg (hW _) (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

lemma level_density_continuous (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ)
    (hW : Continuous W) (hb : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0) :
    Continuous (levelDensity κ W) := by
  have he : levelDensity κ W=fun z => W (levelGraph κ z)/max η (2*Real.sqrt (levelRadicand κ z)) := by
    funext z
    by_cases hh : W (levelGraph κ z)=0
    · simp only [levelDensity,hh,zero_div]
    · have h := hb (levelGraph κ z) (subset_closure hh)
      change η<2*Real.sqrt (levelRadicand κ z) at h
      simp only [levelDensity,max_eq_right h.le]
  rw [he]
  refine (hW.comp (levelGraph_continuous κ)).div
    (continuous_const.max (continuous_const.mul (Real.continuous_sqrt.comp (levelRadicand_continuous κ)))) ?_
  intro z
  exact ne_of_gt (lt_of_lt_of_le hη (le_max_left _ _))

/-- The support lies in the continuous image of the ORIGINAL compact
ambient support under (Q,b,c,d,w). The inverse identity is used only where
the original support bound forces the positive square-root branch. -/
lemma level_density_compact (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ)
    (hW : HasCompactSupport W)
    (hb : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0) :
    HasCompactSupport (levelDensity κ W) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hW.isCompact.image (normalCoordinates_continuous κ))
  intro z hz
  have hw : W (levelGraph κ z)≠0 := by
    intro hzero
    exact hz (by simp only [levelDensity,hzero,zero_div])
  have hxt : levelGraph κ z∈tsupport W := subset_closure hw
  have h := hb (levelGraph κ z) hxt
  change η<2*Real.sqrt (levelRadicand κ z) at h
  have hs : 0<Real.sqrt (levelRadicand κ z) := by linarith
  have hr : 0<levelRadicand κ z := Real.sqrt_pos.mp hs
  exact ⟨levelGraph κ z,hxt,normal_level_inverse κ z hr.le⟩

end ActualOriginalJointLevelDensity318
