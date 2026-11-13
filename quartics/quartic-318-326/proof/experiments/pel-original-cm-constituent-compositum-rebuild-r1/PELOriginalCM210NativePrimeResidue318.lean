module
public import PELOriginalCM210PrimeSpan318
public section
noncomputable section
namespace PELOriginalCM210NativePrimeResidue318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210PrimeReduction318
variable (p:ℕ) (hp:(p:ℤ)∣210)
@[expose] def nativeReduction : O→+*ZMod p :=
  (reduction p hp).comp integerEquiv.symm.toRingHom
lemma nativeReduction_surjective : Function.Surjective (nativeReduction p hp) :=
  (reduction_surjective p hp).comp integerEquiv.symm.surjective
@[expose] def nativeIdeal : Ideal O := RingHom.ker (nativeReduction p hp)
lemma image_mem (z:R) : integerEquiv z∈nativeIdeal p hp ↔ z∈kernel p hp := by
  change reduction p hp (integerEquiv.symm (integerEquiv z))=0 ↔ reduction p hp z=0
  rw [RingEquiv.symm_apply_apply]
lemma native_mem (z:O) : z∈nativeIdeal p hp ↔ (p:ℤ)∣(integerEquiv.symm z).re :=
  mem_kernel p hp (integerEquiv.symm z)
@[expose] def nativeQuotientEquiv : O⧸nativeIdeal p hp ≃+*ZMod p :=
  RingHom.quotientKerEquivOfSurjective (nativeReduction_surjective p hp)
lemma nativeQuotientEquiv_mk (z:O) :
    nativeQuotientEquiv p hp (Ideal.Quotient.mk _ z)=((integerEquiv.symm z).re:ZMod p) := rfl
lemma nativeQuotient_original (z:R) :
    nativeQuotientEquiv p hp (Ideal.Quotient.mk _ (integerEquiv z))=(z.re:ZMod p) := by
  rw [nativeQuotientEquiv_mk,RingEquiv.symm_apply_apply]
end PELOriginalCM210NativePrimeResidue318
