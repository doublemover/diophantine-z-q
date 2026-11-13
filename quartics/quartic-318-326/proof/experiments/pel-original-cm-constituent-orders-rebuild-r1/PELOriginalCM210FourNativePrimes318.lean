module
public import PELOriginalCM210NativePrimeNorm318
public import PELPrimeNormalizerData318
public section
noncomputable section
namespace PELOriginalCM210FourNativePrimes318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210PrimeReduction318 PELOriginalCM210PrimeSpan318
open PELOriginalCM210NativePrimeResidue318 PELOriginalCM210NativePrimeNorm318
open PELPrimeNormalizerData318
lemma prime_divides (i:Fin 4) : (prime i:ℤ)∣210 := by fin_cases i <;> norm_num [prime]
lemma prime_prime (i:Fin 4) : (prime i).Prime := by fin_cases i <;> norm_num [prime]
instance (i:Fin 4) : NeZero (prime i) := ⟨(prime_prime i).ne_zero⟩
@[expose] def ideal (i:Fin 4) : Ideal O := nativeIdeal (prime i) (prime_divides i)
lemma norm (i:Fin 4) : Ideal.absNorm (ideal i)=prime i := native_norm _ _
lemma nonzero (i:Fin 4) : ideal i≠⊥ := native_nonzero _ _
lemma isPrime (i:Fin 4) : (ideal i).IsPrime := native_prime _ _ (prime_prime i)
@[expose] def residueEquiv (i:Fin 4) : O⧸ideal i ≃+*ZMod (prime i) := nativeQuotientEquiv _ _
lemma original_coordinates (i:Fin 4) (z:R) :
    residueEquiv i (Ideal.Quotient.mk _ (integerEquiv z))=(z.re:ZMod (prime i)) :=
  nativeQuotient_original _ _ z
lemma original_kernel (i:Fin 4) (z:R) :
    integerEquiv z∈ideal i ↔ z∈Ideal.span ({(prime i:R),thetaR}:Set R) := by
  rw [show ideal i=nativeIdeal (prime i) (prime_divides i) from rfl,image_mem,kernel_eq_span]
end PELOriginalCM210FourNativePrimes318
