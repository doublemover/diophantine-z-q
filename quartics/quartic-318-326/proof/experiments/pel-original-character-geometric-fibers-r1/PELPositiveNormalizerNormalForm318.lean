module
public import PELNormalizerDivisorWords318
public section
noncomputable section
namespace PELPositiveNormalizerNormalForm318
open PELPrincipalOrderCoordinates318 PELQuaternionAlgebra318 PELActualOrderNormalizer318
open PELQuaternionNormParity318 PELNormalizerPrimitiveRepresentative318
open PELNormalizerDivisorWords318 PELLevelThreeSimilitudes318 PELNormOneNormalizerIntegral318
set_option maxHeartbeats 1800000

/-- Full exhaustion of the SAME positive rational normalizer, with an
actual rational scalar, original norm-one unit and one of the16 original
prime words. The divisor support is constructed, not supplied. -/
theorem normal_form (u : PELPositiveOrderNormalizer318.positiveNormalizer) :
    ∃ (q : ℚˣ) (v : orderˣ) (label : InertiaLabels318.V),
      reducedNorm ((v:order):B)=1 ∧
      u.val=scalarUnit q*integralUnit v*PELInertiaPrimeWord318.word label := by
  let U : normalizer := ⟨u.val,u.property.1⟩
  obtain ⟨q,a,z,w,hu,ha,hprimitive,hdiv,hnorm⟩ := primitive_representative U
  have hNQ : 0<(integralNorm a:ℚ) := by
    have hh : 0<(q:ℚ)^2*(integralNorm a:ℚ) := by
      rw [←hnorm]
      exact u.property.2
    exact pos_of_mul_pos_left hh (sq_nonneg (q:ℚ))
  have hN : 0<integralNorm a := by exact_mod_cast hNQ
  obtain ⟨label,hlabel⟩ := positive_divisor_word (integralNorm a) hN hdiv
  let W : normalizer := word label
  let X : normalizer := w*W⁻¹
  have hw : reducedNorm (w.val:B)=reducedNorm (W.val:B) := by
    rw [←ha,original_norm]
    change (integralNorm a:ℚ)=reducedNorm (PELInertiaPrimeWord318.word label:B)
    rw [word_norm,hlabel]
    norm_num
  have hx : reducedNorm (X.val:B)=1 := by
    change reducedNorm ((w.val:B)*(↑W.val⁻¹:B))=1
    rw [norm_mul,hw,←norm_mul,Units.val_inv]
    norm_num [reducedNorm]
  refine ⟨q,integralUnitOfNormOne X hx,label,integralUnitOfNormOne_norm X hx,?_⟩
  rw [integralUnitOfNormOne_value]
  change U.val=scalarUnit q*(w.val*W.val⁻¹)*W.val
  rw [hu]
  simp only [mul_assoc,inv_mul_cancel,mul_one]

/-- The actual label is forced by the original norm-parity homomorphism,
so the normal form does not introduce an unrelated16-element parameter. -/
theorem normal_form_parity (u : PELPositiveOrderNormalizer318.positiveNormalizer)
    (q : ℚˣ) (v : orderˣ) (label : InertiaLabels318.V)
    (hv : reducedNorm ((v:order):B)=1)
    (hu : u.val=scalarUnit q*integralUnit v*PELInertiaPrimeWord318.word label) :
    PELPositiveOrderNormalizer318.parity u=Multiplicative.ofAdd label := by
  change PELQuaternionNormParity318.parity u.val=label
  rw [hu,parity_mul,parity_mul,parity_scalar,parity_norm_one v hv,parity_word,zero_add,zero_add]

/-- EXACT kernel classification for the full positive normalizer. No
outside210 support premise or unspecified local maximal-order theorem remains. -/
theorem parity_kernel_iff (u : PELPositiveOrderNormalizer318.positiveNormalizer) :
    PELPositiveOrderNormalizer318.parity u=1 ↔
      ∃ (q : ℚˣ) (v : orderˣ),reducedNorm ((v:order):B)=1 ∧ u.val=scalarUnit q*integralUnit v := by
  constructor
  · intro hp
    obtain ⟨q,v,label,hv,hu⟩ := normal_form u
    have hl : label=0 := by
      have he := normal_form_parity u q v label hv hu
      rw [hp] at he
      exact (congrArg Multiplicative.toAdd he).symm
    subst label
    refine ⟨q,v,hv,?_⟩
    simpa [PELInertiaPrimeWord318.word] using hu
  · rintro ⟨q,v,hv,hu⟩
    change PELQuaternionNormParity318.parity u.val=0
    rw [hu,parity_mul,parity_scalar,parity_norm_one v hv,zero_add]
end PELPositiveNormalizerNormalForm318
