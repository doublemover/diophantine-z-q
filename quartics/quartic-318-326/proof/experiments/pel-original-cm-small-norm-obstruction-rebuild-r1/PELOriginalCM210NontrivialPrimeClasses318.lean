module
public import PELOriginalCM210SmallIdealNonprincipal318
public import PELOriginalCM210NativePrimeClasses318
public section
noncomputable section
namespace PELOriginalCM210NontrivialPrimeClasses318
open PELOriginalCM210NativeIntegerOrder318 PELOriginalCM210FourNativePrimes318
open PELOriginalCM210NativePrimeClasses318 PELOriginalCM210SmallNormObstruction318
open PELOriginalCM210SmallIdealNonprincipal318 PELPrimeNormalizerData318
@[expose] def divisorIndex : Fin 4→Fin 14 := ![0,1,2,4]
lemma same_prime (i:Fin 4) : divisor (divisorIndex i)=prime i := by
  fin_cases i <;> rfl
lemma original_nonprincipal (i:Fin 4) : ¬(ideal i).IsPrincipal := by
  apply no_principal_of_norm _ _ (norm i)
  · fin_cases i <;> norm_num [prime]
  · intro r
    simpa only [same_prime] using divisor_nonsquare (divisorIndex i) r
lemma class_nontrivial (i:Fin 4) : primeClass i≠1 := by
  intro h
  exact original_nonprincipal i ((ClassGroup.mk0_eq_one_iff (nonzeroIdeal i).property).mp h)
end PELOriginalCM210NontrivialPrimeClasses318
