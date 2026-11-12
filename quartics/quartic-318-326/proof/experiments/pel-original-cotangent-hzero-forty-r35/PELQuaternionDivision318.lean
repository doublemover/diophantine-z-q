module
public import PELQuaternionAnisotropy318
public section
noncomputable section
namespace PELQuaternionDivision318
open PELQuaternionAlgebra318 PELQuaternionAnisotropy318 QuaternionAlgebra
set_option maxHeartbeats 1000000

@[expose] def reciprocal (x : B) : B := (reducedNorm x)⁻¹ • star x

theorem norm_identity_left (x : B) :
    star x*x=algebraMap ℚ B (reducedNorm x) := by
  ext <;> simp [reducedNorm,QuaternionAlgebra.algebraMap_eq] <;> ring

theorem mul_reciprocal (x : B) (hx : x≠0) : x*reciprocal x=1 := by
  have hn := reducedNorm_ne_zero x hx
  calc
    x*reciprocal x=(reducedNorm x)⁻¹ • (x*star x) := by
      exact mul_smul_comm _ _ _
    _ = (reducedNorm x)⁻¹ • algebraMap ℚ B (reducedNorm x) := by rw [norm_identity]
    _ = 1 := by rw [Algebra.smul_def,← map_mul,inv_mul_cancel₀ hn,map_one]

theorem reciprocal_mul (x : B) (hx : x≠0) : reciprocal x*x=1 := by
  have hn := reducedNorm_ne_zero x hx
  calc
    reciprocal x*x=(reducedNorm x)⁻¹ • (star x*x) := by
      exact smul_mul_assoc _ _ _
    _ = (reducedNorm x)⁻¹ • algebraMap ℚ B (reducedNorm x) := by rw [norm_identity_left]
    _ = 1 := by rw [Algebra.smul_def,← map_mul,inv_mul_cancel₀ hn,map_one]

/-- The specific rational quaternion algebra is division: every nonzero
actual element has the displayed two-sided inverse. No abstract division
algebra or local classification is supplied as an input. -/
theorem every_nonzero_isUnit (x : B) (hx : x≠0) : IsUnit x :=
  ⟨⟨x,reciprocal x,mul_reciprocal x hx,reciprocal_mul x hx⟩,rfl⟩
end PELQuaternionDivision318
