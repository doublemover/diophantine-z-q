module
public import PELPrimitiveRationalCoordinates318
public section
noncomputable section
namespace PELPrimitiveNormalizerNorm318
open PELPrincipalOrderCoordinates318 PELPrincipalOrderPerfect318 PELQuaternionAlgebra318
open PELActualOrderNormalizer318 PELNormalizerQuadraticCertificates318 PELNormalizerTraceIntegral318
open PELLevelThreeSimilitudes318 PELQuaternionDivision318
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem embed_conjugate (a : Coordinates) : embed (conjugateCoordinates a)=star (embed a) := by
  ext <;> simp [conjugateCoordinates,embed] <;> push_cast <;> ring

theorem embed_zsmul (n : ℤ) (a : Coordinates) : embed (n • a)=(n:ℚ) • embed a := by
  ext <;> simp [embed,Pi.smul_apply,zsmul_eq_mul] <;> push_cast <;> ring

/-- Clearing the ACTUAL reduced norm from the original conjugation gives
the literal original-coordinate numerator, with its sign and no estimate. -/
theorem numerator_identity (u : normalizer) (a : Coordinates)
    (ha : embed a=(u.val:B)) (j : Fin 4) :
    embed (product (product a (basis j)) (conjugateCoordinates a))=
      (integralNorm a:ℚ) • ((u.val:B)*embed (basis j)*(↑u.val⁻¹:B)) := by
  have hN : (integralNorm a:ℚ)≠0 := by
    rw [←original_norm,ha]
    exact PELQuaternionAnisotropy318.reducedNorm_ne_zero (u.val:B) u.val.ne_zero
  rw [embed_mul,embed_mul,embed_conjugate,unit_inverse,←ha,reciprocal,original_norm]
  rw [mul_smul_comm,smul_smul,mul_inv_cancel₀ hN,one_smul]

/-- Each integer numerator is divisible by the ORIGINAL norm because the
whole conjugation map preserves the original order, not merely one lattice. -/
theorem norm_divides_numerator (u : normalizer) (a : Coordinates)
    (ha : embed a=(u.val:B)) (k : Fin 16) : integralNorm a∣numerator a k := by
  let x : order := ⟨(u.val:B)*embed (basis (row k))*(↑u.val⁻¹:B),
    (u.property (embed (basis (row k))) ⟨basis (row k),rfl⟩).1⟩
  let b : Coordinates := coordinatesEquiv.symm x
  have hb : embed b=(x:B) := congrArg order.subtype (coordinatesEquiv.apply_symm_apply x)
  have he : embed (product (product a (basis (row k))) (conjugateCoordinates a))=
      embed (integralNorm a • b) := by
    rw [embed_zsmul,hb]
    exact numerator_identity u a ha (row k)
  have hc := congrFun (embed_injective he) (col k)
  refine ⟨b (col k),?_⟩
  simpa only [numerator,Pi.smul_apply,zsmul_eq_mul] using hc

/-- The actual primitive integral normalizer norm divides210. All16
conjugation-coordinate numerators and the full integer Bezout witness are used. -/
theorem primitive_norm_support (u : normalizer) (a z : Coordinates)
    (ha : embed a=(u.val:B)) (hprimitive : ∑ i : Fin 4,z i*a i=1) : integralNorm a∣210 :=
  primitive_norm_divides210 a z (integralNorm a) hprimitive (norm_divides_numerator u a ha)
end PELPrimitiveNormalizerNorm318
