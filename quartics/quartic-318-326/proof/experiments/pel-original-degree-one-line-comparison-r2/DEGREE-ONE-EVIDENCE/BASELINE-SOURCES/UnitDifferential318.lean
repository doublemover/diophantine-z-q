module
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace UnitDifferential318
set_option maxHeartbeats 200000
variable {R T M : Type*} [CommRing R] [CommRing T] [AddCommGroup M]
  [Algebra R T] [Module T M] [Module R M] [IsScalarTower R T M]

theorem inverse (d : Derivation R T M) (z v : T) (hzv : z*v=1) :
    d v = -(v^2) • d z := by
  have hd : z • d v = -(v • d z) := by
    apply eq_neg_iff_add_eq_zero.mpr
    rw [←d.leibniz,hzv,d.map_one_eq_zero]
  calc
    d v = (v*z) • d v := by rw [mul_comm,hzv,one_smul]
    _ = v • (z • d v) := by rw [smul_smul]
    _ = v • (-(v • d z)) := by rw [hd]
    _ = -(v^2) • d z := by simp [smul_smul,pow_two]

/-- Differentiate the actual reciprocal coordinate without a field or division operation. -/
theorem ratio (d : Derivation R T M) (x z v : T) (hzv : z*v=1) :
    d (x*v) = v • d x - (x*v^2) • d z := by
  rw [d.leibniz,inverse d z v hzv]
  simp [smul_smul,sub_eq_add_neg,add_comm]

end UnitDifferential318
