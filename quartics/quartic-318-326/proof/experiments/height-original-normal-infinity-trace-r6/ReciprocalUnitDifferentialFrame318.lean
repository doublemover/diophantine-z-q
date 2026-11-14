module
public import IntegralNormalSourceDifferentialFrame318
public import UnitReciprocalDifferential318
public section
noncomputable section
namespace ReciprocalUnitDifferentialFrame318
variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- Actual inverse-coordinate differentiation, over any base ring. -/
theorem inverse_D (u : Bˣ) :
    KaehlerDifferential.D R B (↑u⁻¹:B)=
      -((↑u⁻¹:B)^2) • KaehlerDifferential.D R B (u:B) :=
  UnitReciprocalDifferential318.differential (R:=R) u

theorem forward_D (u : Bˣ) :
    KaehlerDifferential.D R B (u:B)=
      -((u:B)^2) • KaehlerDifferential.D R B (↑u⁻¹:B) := by
  simpa only [inv_inv] using (inverse_D (R:=R) u⁻¹)

variable (e : KaehlerDifferential R B ≃ₗ[B] B) (u : Bˣ)
  (he : e (KaehlerDifferential.D R B (u:B))=1)

include he in
theorem reciprocal_D_coefficient :
    e (KaehlerDifferential.D R B (↑u⁻¹:B))=-((↑u⁻¹:B)^2) := by
  rw [inverse_D,map_smul,he,smul_eq_mul,mul_one]

include he in
/-- Equality of the WHOLE differential, retaining the sign and square
Jacobian. The two coordinates are genuinely inverse on this ring. -/
theorem reconstruction (ω : KaehlerDifferential R B) :
    (-(u:B)^2*e ω) • KaehlerDifferential.D R B (↑u⁻¹:B)=ω := by
  have ht : e ω • KaehlerDifferential.D R B (u:B)=ω := by
    apply e.injective
    rw [map_smul,he,smul_eq_mul,mul_one]
  rw [forward_D,smul_smul] at ht
  calc
    _ = (e ω * (-(u:B)^2)) • KaehlerDifferential.D R B (↑u⁻¹:B) := by rw [mul_comm]
    _ = ω := ht

/-- The reciprocal frame is PRODUCED from the actual inverse-coordinate
relation, with no independent unit ambiguity or invertibility assumption
on 2 in the unlocalized coefficient ring. -/
@[expose] def reciprocalFrame : KaehlerDifferential R B ≃ₗ[B] B where
  toFun ω := -(u:B)^2*e ω
  invFun z := z • KaehlerDifferential.D R B (↑u⁻¹:B)
  map_add' ω η := by rw [map_add,mul_add]
  map_smul' z ω := by rw [map_smul]; change _=z*_; ring
  left_inv ω := reconstruction e u he ω
  right_inv z := by
    rw [map_smul,reciprocal_D_coefficient e u he,smul_eq_mul]
    calc
      _ = z * (((u:B)*(↑u⁻¹:B))^2) := by ring
      _ = z := by rw [Units.mul_inv,one_pow,mul_one]

@[simp] theorem reciprocalFrame_D :
    reciprocalFrame e u he (KaehlerDifferential.D R B (↑u⁻¹:B))=1 := by
  have h := (reciprocalFrame e u he).apply_symm_apply 1
  simpa only [one_smul] using h

lemma reciprocalFrame_value (ω : KaehlerDifferential R B) :
    reciprocalFrame e u he ω=-(u:B)^2*e ω := rfl
end ReciprocalUnitDifferentialFrame318
