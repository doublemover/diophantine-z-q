module
public import PELQuaternionRealRepresentation318
public section
noncomputable section
namespace PELQuaternionIntegralOrder318
open PELQuaternionAlgebra318 PELQuaternionAlternatingForm318 QuaternionAlgebra
set_option maxHeartbeats 1000000

/-- The literal four-coordinate integral order; maximality is deliberately
not asserted. Its nonprincipal trace pairing is proved below. -/
abbrev IntegralCoordinates := QuaternionAlgebra ℤ (-210) 0 5
@[expose] def inclusion : IntegralCoordinates →+* B where
  toFun x := ⟨x.re,x.imI,x.imJ,x.imK⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> push_cast <;> ring

theorem inclusion_injective : Function.Injective inclusion := by
  intro x y h
  apply QuaternionAlgebra.ext
  · exact_mod_cast congrArg QuaternionAlgebra.re h
  · exact_mod_cast congrArg QuaternionAlgebra.imI h
  · exact_mod_cast congrArg QuaternionAlgebra.imJ h
  · exact_mod_cast congrArg QuaternionAlgebra.imK h

@[expose] def standardOrder : Subring B := inclusion.range

/-- The same Rosati operation preserves this concrete order. This does not
identify it with the maximal order required by the PEL moduli problem. -/
theorem rosati_integral (x : IntegralCoordinates) :
    rosati (inclusion x)=inclusion ⟨x.re,-x.imI,x.imJ,x.imK⟩ := by
  rw [rosati_coordinates]
  ext <;> simp [inclusion]

@[expose] def integralPairing (x y : IntegralCoordinates) : ℤ :=
  2*(x.imI*y.re-x.re*y.imI+5*x.imJ*y.imK-5*x.imK*y.imJ)

theorem pairing_integral (x y : IntegralCoordinates) :
    pairing (inclusion x) (inclusion y)=(integralPairing x y:ℚ) := by
  rw [coordinates]
  simp [inclusion,integralPairing]

/-- A concrete obstruction to falsely declaring the evident integral basis
principally polarized: every pairing against1 is even, whereas the integral
real-coordinate functional takes value1 there. A maximal order and the
correct perfect lattice must genuinely be constructed. -/
theorem standard_pairing_not_perfect :
    ¬∃ x : IntegralCoordinates,∀ y : IntegralCoordinates,
      integralPairing x y=y.re := by
  rintro ⟨x,hx⟩
  have h := hx 1
  norm_num [integralPairing] at h
  omega
end PELQuaternionIntegralOrder318
