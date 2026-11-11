module
public import ActualOriginalNormalSupportBounds318
public section
noncomputable section
namespace ActualOriginalWholeNormalSubstitution318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318 ActualOriginalJointLevelDensity318
open ActualOriginalNormalJacobian318 ActualOriginalIntervalSubstitution318 ActualOriginalNormalSupportBounds318
open MeasureTheory
set_option maxHeartbeats 16000000

lemma whole_integral_eq_positive_interval {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ→E) (A B : ℝ) (hAB : A≤B)
    (hz : ∀x,x∉Set.Icc A B → f x=0) :
    (∫x,f x)=∫x in A..B,f x := by
  rw [intervalIntegral.integral_of_le hAB,←integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hz).symm

/-- Genuine WHOLE-line substitution for the ORIGINAL a-coordinate at
EVERY four-coordinate parameter v. All cutoffs are constructed uniformly
from the same original compact weight support. Arbitrary continuous
vector-valued phases are retained literally. -/
theorem actual_original_whole_normal_substitution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ η : ℝ) (hη : 0<η) (W : Coordinates ℝ→ℝ)
    (hW : Continuous W) (hWc : HasCompactSupport W)
    (hb : ∀x∈tsupport W,η<ActualQuadricTaylor318.gradient κ x 0)
    (phase : ℝ→E) (hphase : Continuous phase) (v : Parameters) :
    (∫a : ℝ,W (assemble a v) • phase (equation κ (assemble a v)))=
      ∫s : ℝ,levelDensity κ W (s,v) • phase s := by
  obtain ⟨A,B,hA,hAB,hbounds⟩ := actual_uniform_normal_bounds κ η hη W hWc hb
  have hends := actual_normal_endpoint_order κ A B hA hAB v
  calc
    _ = ∫a in A..B,W (assemble a v) • phase (equation κ (assemble a v)) := by
      apply whole_integral_eq_positive_interval _ A B hAB.le
      intro a ha
      rw [source_outside_normal_bounds W A B hbounds v a ha,zero_smul]
    _ = ∫s in equation κ (assemble A v)..equation κ (assemble B v),
        levelDensity κ W (s,v) • phase s :=
      original_positive_interval_substitution κ η hη W hW hb phase hphase v A B hA hAB.le
    _ = _ := by
      symm
      apply whole_integral_eq_positive_interval _ _ _ hends.le
      intro s hs
      rw [density_outside_normal_bounds κ W A B hA hAB hbounds v s hs,zero_smul]

end ActualOriginalWholeNormalSubstitution318
