module
public import ActualOriginalGaussianMassRecovery318
public section
noncomputable section
namespace ActualOriginalNormalJacobian318
open QuadricCRTAssembly318 ActualOriginalPositiveQuadricChart318 ActualOriginalNormalLevelChart318
open ActualOriginalJointLevelDensity318
set_option maxHeartbeats 16000000
@[expose] def assemble (a : ℝ) (v : Parameters) : Coordinates ℝ := ((a,v.1),v.2.1,v.2.2)
lemma original_normal_polynomial (κ a : ℝ) (v : Parameters) :
    equation κ (assemble a v)=a^2-radicand κ v := by
  dsimp [equation,assemble,radicand]
  ring
lemma original_normal_derivative (κ a : ℝ) (v : Parameters) :
    HasDerivAt (fun t => equation κ (assemble t v)) (2*a) a :=
  actual_normal_derivative κ a v.1 v.2.1.1 v.2.1.2 v.2.2
lemma actual_original_jacobian_cancellation (κ a : ℝ) (ha : 0<a)
    (W : Coordinates ℝ→ℝ) (v : Parameters) :
    (2*a)*levelDensity κ W (equation κ (assemble a v),v)=W (assemble a v) := by
  have hcoord : (equation κ (assemble a v),v)=normalCoordinates κ (assemble a v) := rfl
  have hg := original_normal_inverse κ (assemble a v) ha.le
  have hr := original_normal_radicand κ (assemble a v)
  change levelRadicand κ (normalCoordinates κ (assemble a v))=a^2 at hr
  rw [hcoord,levelDensity,hg,hr,Real.sqrt_sq ha.le]
  have hn : 2*a≠0 := ne_of_gt (mul_pos (by norm_num) ha)
  field_simp [hn] <;> ring

/-- Cancellation uses the actual original normal derivative2a and the
actual inverse level chart, including a vector-valued phase unchanged. -/
lemma original_phase_jacobian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ a : ℝ) (ha : 0<a) (W : Coordinates ℝ→ℝ) (v : Parameters) (phase : ℝ→E) :
    (2*a) • (levelDensity κ W (equation κ (assemble a v),v) •
      phase (equation κ (assemble a v)))=
    W (assemble a v) • phase (equation κ (assemble a v)) := by
  rw [smul_smul,actual_original_jacobian_cancellation κ a ha W v]
end ActualOriginalNormalJacobian318
