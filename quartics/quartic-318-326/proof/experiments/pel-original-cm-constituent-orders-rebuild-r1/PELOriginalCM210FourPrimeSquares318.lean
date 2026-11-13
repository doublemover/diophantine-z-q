module
public import PELOriginalCM210PrimeSquare318
public import PELOriginalCM210PrimeIdealTransport318
public import PELOriginalCM210FourNativePrimes318
public section
noncomputable section
namespace PELOriginalCM210FourPrimeSquares318
open PELOriginalCM210IntegralConjugation318 PELOriginalCM210NativeIntegerOrder318
open PELOriginalCM210PrimeReduction318 PELOriginalCM210PrimeSquare318
open PELOriginalCM210NativePrimeResidue318 PELOriginalCM210PrimeIdealTransport318
open PELOriginalCM210FourNativePrimes318 PELPrimeNormalizerData318
@[expose] def bezoutA : Fin 4→ℤ := ![53,47,17,13]
@[expose] def bezoutC : Fin 4→ℤ := ![1,2,2,3]
lemma bezout (i:Fin 4) : bezoutA i*(prime i:ℤ)^2-bezoutC i*210=prime i := by
  fin_cases i <;> norm_num [bezoutA,bezoutC,prime]
lemma original_square (i:Fin 4) :
    kernel (prime i) (prime_divides i)*kernel (prime i) (prime_divides i)=
      Ideal.span ({(prime i:R)}:Set R) :=
  square_eq_principal _ _ _ _ (bezout i)
lemma native_square (i:Fin 4) : (ideal i)^2=Ideal.span ({(prime i:O)}:Set O) := by
  have h := congrArg (Ideal.map integerEquiv.toRingHom) (original_square i)
  simp only [Ideal.map_mul,map_kernel,map_principal] at h
  simpa only [pow_two,ideal] using h
end PELOriginalCM210FourPrimeSquares318
