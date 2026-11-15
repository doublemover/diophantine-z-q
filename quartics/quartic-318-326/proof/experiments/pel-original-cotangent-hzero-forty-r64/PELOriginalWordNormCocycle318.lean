module
public import PELActualSquareNormActionKernel318
public section
noncomputable section
namespace PELOriginalWordNormCocycle318
open PELQuaternionAlgebra318 PELQuaternionNormParity318 PELPrimeNormalizerData318
open PELPositiveOrderNormalizer318
set_option maxHeartbeats 1700000
open scoped BigOperators

@[expose] def bitNorm (p : ℚ) (z : ZMod 2) : ℚ := if z=0 then 1 else p
@[expose] def commonFactor (p : ℚ) (a b : ZMod 2) : ℚ := if a=0 ∨ b=0 then 1 else p
@[expose] def wordNorm (v : InertiaLabels318.V) : ℚ := ∏ i : Fin 4,bitNorm (prime i) (v i)
@[expose] def squareFactor (v w : InertiaLabels318.V) : ℚ :=
  ∏ i : Fin 4,commonFactor (prime i) (v i) (w i)

theorem bit_identity (p : ℚ) (a b : ZMod 2) :
    bitNorm p a*bitNorm p b=bitNorm p (a+b)*commonFactor p a b^2 := by
  fin_cases a <;> fin_cases b <;> norm_num [bitNorm,commonFactor] <;> ring

theorem wordNorm_nonzero (v : InertiaLabels318.V) : wordNorm v≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  unfold bitNorm
  split_ifs
  · exact one_ne_zero
  · exact prime_ne_zero i

theorem squareFactor_nonzero (v w : InertiaLabels318.V) : squareFactor v w≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  unfold commonFactor
  split_ifs
  · exact one_ne_zero
  · exact prime_ne_zero i

/-- The original ordered quaternion word has its exact rational norm,
not just the same four parity bits. -/
theorem original_norm (v : InertiaLabels318.V) :
    reducedNorm ((PELPositiveOrderNormalizer318.word v).val:B)=wordNorm v := by
  have hb (i : Fin 4) : reducedNorm
      ((if v i=0 then 1 else PELPrimeNormalizerData318.rationalUnit i):Bˣ)=bitNorm (prime i) (v i) := by
    by_cases h : v i=0
    · simp [h,bitNorm,reducedNorm]
    · simpa only [h,if_false,bitNorm] using element_norm i
  change reducedNorm ((PELInertiaPrimeWord318.word v:Bˣ):B)= _
  simp only [PELInertiaPrimeWord318.word,Units.val_mul,norm_mul,hb,
    wordNorm,Fin.prod_univ_four]

/-- A concrete nonzero rational scalar accounts for every binary carry
when original labels are added. -/
theorem norm_cocycle (v w : InertiaLabels318.V) :
    wordNorm v*wordNorm w=wordNorm (v+w)*squareFactor v w^2 := by
  calc
    wordNorm v*wordNorm w=
        ∏ i : Fin 4,bitNorm (prime i) (v i)*bitNorm (prime i) (w i) :=
      (Finset.prod_mul_distrib).symm
    _ = ∏ i : Fin 4,bitNorm (prime i) (v i+w i)*commonFactor (prime i) (v i) (w i)^2 := by
      apply Finset.prod_congr rfl
      intro i hi
      exact bit_identity _ _ _
    _ = wordNorm (v+w)*squareFactor v w^2 := by
      rw [Finset.prod_mul_distrib,Finset.prod_pow] <;> rfl

theorem norm_unit_inverse (u : Bˣ) : reducedNorm (↑u⁻¹:B)=(reducedNorm (u:B))⁻¹ := by
  have hn := PELQuaternionAnisotropy318.reducedNorm_ne_zero (u:B) u.ne_zero
  have hh : reducedNorm (u:B)*reducedNorm (↑u⁻¹:B)=1 := by
    rw [←norm_mul,Units.val_inv] <;> norm_num [reducedNorm]
  apply mul_left_cancel₀ hn
  rw [hh,mul_inv_cancel₀ hn]

/-- The full original discrepancy word has ACTUAL square norm, so the
proved analytic action-kernel theorem applies without parity support. -/
theorem discrepancy_square (v w : InertiaLabels318.V) :
    reducedNorm (((PELPositiveOrderNormalizer318.word (v+w))⁻¹*
      PELPositiveOrderNormalizer318.word v*PELPositiveOrderNormalizer318.word w).val:B)=
      squareFactor v w^2 := by
  change reducedNorm ((((PELPositiveOrderNormalizer318.word (v+w)).val⁻¹:Bˣ):B)*
    ((PELPositiveOrderNormalizer318.word v).val:B)*((PELPositiveOrderNormalizer318.word w).val:B))= _
  rw [norm_mul,norm_mul,norm_unit_inverse,original_norm,original_norm,original_norm]
  calc
    _ = (wordNorm (v+w))⁻¹*(wordNorm v*wordNorm w) := by ring
    _ = (wordNorm (v+w))⁻¹*(wordNorm (v+w)*squareFactor v w^2) := by rw [norm_cocycle]
    _ = squareFactor v w^2 := by rw [←mul_assoc,inv_mul_cancel₀ (wordNorm_nonzero _),one_mul]
end PELOriginalWordNormCocycle318
