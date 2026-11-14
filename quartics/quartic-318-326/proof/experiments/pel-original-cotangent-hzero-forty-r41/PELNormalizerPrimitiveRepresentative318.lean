module
public import PELPrimitiveNormalizerNorm318
public section
noncomputable section
namespace PELNormalizerPrimitiveRepresentative318
open PELPrincipalOrderCoordinates318 PELQuaternionAlgebra318 PELActualOrderNormalizer318
open PELNormalizerTraceIntegral318 PELPrimitiveRationalCoordinates318
open PELSquareNormNormalizerKernel318 PELQuaternionNormParity318 PELLevelThreeSimilitudes318
open PELPrimitiveNormalizerNorm318
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem rationalCoordinates_ne_zero (u : Bˣ) : rationalCoordinates (u:B)≠0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  norm_num [rationalCoordinates] at h0 h1 h2 h3
  apply u.ne_zero
  ext <;> change _ = 0 <;> linarith

theorem original_reconstruction (x : B) (q : ℚ) (a : Coordinates)
    (h : ∀ i,rationalCoordinates x i=q*(a i:ℚ)) : x=q • embed a := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  norm_num [rationalCoordinates] at h0 h1 h2 h3
  ext <;> simp [embed] <;> linarith

/-- Every actual rational normalizer has a scalar multiple with primitive
integer coordinates in the SAME order; its norm has literal support210. -/
theorem primitive_representative (u : normalizer) :
    ∃ (q : ℚˣ) (a z : Coordinates) (w : normalizer),
      u.val=scalarUnit q*w.val ∧ embed a=(w.val:B) ∧
      (∑ i : Fin 4,z i*a i=1) ∧ integralNorm a∣210 ∧
      reducedNorm (u.val:B)=(q:ℚ)^2*(integralNorm a:ℚ) := by
  obtain ⟨q,a,z,hq,hcoord,hprim⟩ := primitive_rational
    (rationalCoordinates (u.val:B)) (rationalCoordinates_ne_zero u.val)
  let Q : ℚˣ := Units.mk0 q hq
  let w : normalizer := ⟨scalarUnit Q⁻¹*u.val,normalizer.mul_mem (scalar_mem Q⁻¹) u.property⟩
  have hx : (u.val:B)=q • embed a := original_reconstruction _ q a hcoord
  have ha : embed a=(w.val:B) := by
    change embed a=algebraMap ℚ B q⁻¹*(u.val:B)
    rw [←Algebra.smul_def,hx,smul_smul,inv_mul_cancel₀ hq,one_smul]
  have hu : u.val=scalarUnit Q*w.val := by
    change u.val=scalarUnit Q*(scalarUnit Q⁻¹*u.val)
    have hinv : scalarUnit Q⁻¹=(scalarUnit Q)⁻¹ := map_inv (Units.map (algebraMap ℚ B).toMonoidHom) Q
    rw [hinv,←mul_assoc,mul_inv_cancel,one_mul]
  refine ⟨Q,a,z,w,hu,ha,hprim,primitive_norm_support w a z ha hprim,?_⟩
  rw [hu]
  change reducedNorm (algebraMap ℚ B (Q:ℚ)*(w.val:B))=(Q:ℚ)^2*(integralNorm a:ℚ)
  rw [norm_mul,norm_scalar,←ha,original_norm]
end PELNormalizerPrimitiveRepresentative318
