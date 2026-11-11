module
public import PELIntegralUnitSpan318
public section
noncomputable section
namespace PELNormalizerTraceIntegral318
open PELPrincipalOrderCoordinates318 PELQuaternionAlgebra318 PELActualOrderNormalizer318
open PELPrincipalOrderPerfect318 PELQuaternionDivision318
set_option maxHeartbeats 1600000

/-- Coordinates in the original HALF-INTEGRAL order basis, now overQ. -/
@[expose] def rationalCoordinates (x : B) : Fin 4 → ℚ :=
  ![x.re-x.imJ,x.imI-5*x.imK,2*x.imJ,10*x.imK]

theorem rationalCoordinates_embed (a : Coordinates) (i : Fin 4) :
    rationalCoordinates (embed a) i=(a i:ℚ) := by
  fin_cases i <;> simp [rationalCoordinates,embed] <;> ring

/-- Trace of the actual linear map z↦x*z*y, computed on the SAME original
order basis. This identity does not invoke an abstract adjoint representation. -/
theorem sandwich_trace (x y : B) :
    rationalCoordinates (x*embed (basis 0)*y) 0+
    rationalCoordinates (x*embed (basis 1)*y) 1+
    rationalCoordinates (x*embed (basis 2)*y) 2+
    rationalCoordinates (x*embed (basis 3)*y) 3 = reducedTrace x*reducedTrace y := by
  norm_num [rationalCoordinates,embed,basis,reducedTrace,Pi.single_apply]
  <;> ring

theorem unit_inverse (u : Bˣ) : (↑u⁻¹:B)=reciprocal (u:B) := by
  calc
    (↑u⁻¹:B)=(↑u⁻¹:B)*1 := (mul_one _).symm
    _ = (↑u⁻¹:B)*((u:B)*reciprocal (u:B)) :=
      congrArg (fun z : B => (↑u⁻¹:B)*z) (mul_reciprocal (u:B) u.ne_zero).symm
    _ = reciprocal (u:B) := by rw [←mul_assoc,Units.inv_val,one_mul]

theorem inverse_trace (u : Bˣ) :
    reducedTrace (↑u⁻¹:B)=(reducedNorm (u:B))⁻¹*reducedTrace (u:B) := by
  rw [unit_inverse]
  simp [reciprocal,reducedTrace]
  <;> ring

/-- Integrality comes from the actual integer matrix of conjugation onO.
No integrality of the quaternion u itself is assumed. -/
theorem conjugation_trace_integral (u : normalizer) :
    ∃ n : ℤ,reducedTrace (u.val:B)^2/reducedNorm (u.val:B)=(n:ℚ) := by
  let a : Fin 4 → Coordinates := fun j => coordinatesEquiv.symm
    ⟨(u.val:B)*embed (basis j)*(↑u.val⁻¹:B),
      (u.property (embed (basis j)) ⟨basis j,rfl⟩).1⟩
  have ha (j : Fin 4) : embed (a j)=(u.val:B)*embed (basis j)*(↑u.val⁻¹:B) := by
    exact congrArg order.subtype (coordinatesEquiv.apply_symm_apply
      ⟨(u.val:B)*embed (basis j)*(↑u.val⁻¹:B),
        (u.property (embed (basis j)) ⟨basis j,rfl⟩).1⟩)
  have ht := sandwich_trace (u.val:B) (↑u.val⁻¹:B)
  rw [←ha 0,←ha 1,←ha 2,←ha 3,
    rationalCoordinates_embed,rationalCoordinates_embed,rationalCoordinates_embed,rationalCoordinates_embed,
    inverse_trace] at ht
  refine ⟨a 0 0+a 1 1+a 2 2+a 3 3,?_⟩
  push_cast
  rw [ht]
  ring

/-- Rational square-integrality is used ONLY in the commutative fieldQ. -/
theorem rational_of_square_integral (q : ℚ) (n : ℤ) (h : q^2=(n:ℚ)) :
    ∃ z : ℤ,q=(z:ℚ) := by
  have hi : IsIntegral ℤ (q^2) := by
    rw [h]
    exact isIntegral_algebraMap
  have hq : IsIntegral ℤ q := hi.of_pow (by decide : 0<2)
  obtain ⟨z,hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq
  exact ⟨z,hz.symm⟩

theorem norm_sign_trace_integral (u : normalizer)
    (hu : reducedNorm (u.val:B)=1 ∨ reducedNorm (u.val:B)= -1) :
    ∃ z : ℤ,reducedTrace (u.val:B)=(z:ℚ) := by
  obtain ⟨n,hn⟩ := conjugation_trace_integral u
  rcases hu with hu|hu
  · rw [hu,div_one] at hn
    exact rational_of_square_integral _ n hn
  · have hs : reducedTrace (u.val:B)^2=((-n:ℤ):ℚ) := by
      rw [hu] at hn
      push_cast
      linarith
    exact rational_of_square_integral _ (-n) hs
end PELNormalizerTraceIntegral318
