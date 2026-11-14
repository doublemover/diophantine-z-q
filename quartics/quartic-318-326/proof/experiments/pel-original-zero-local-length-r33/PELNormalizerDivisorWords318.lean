module
public import PELNormalizerPrimitiveRepresentative318
public section
noncomputable section
namespace PELNormalizerDivisorWords318
open PELQuaternionAlgebra318 PELQuaternionNormParity318
open scoped BigOperators
set_option maxHeartbeats 1800000

theorem word_norm (v : InertiaLabels318.V) :
    reducedNorm (PELInertiaPrimeWord318.word v:B)=(InertiaLabels318.divisor v:ℚ) := by
  have h (j : Fin 4) : reducedNorm
      (↑(if v j=0 then (1:Bˣ) else PELPrimeNormalizerData318.rationalUnit j):B)=
      (if v j=0 then 1 else (PELPrimeNormalizerData318.prime j:ℚ)) := by
    split_ifs
    · norm_num [reducedNorm]
    · exact PELPrimeNormalizerData318.element_norm j
  simp only [PELInertiaPrimeWord318.word,Units.val_mul,norm_mul,h]
  norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,
    InertiaLabels318.primes,PELPrimeNormalizerData318.prime]
  <;> push_cast <;> rfl

/-- Every positive divisor of210 is one of the16 ORIGINAL prime words.
This is an exhaustive integer statement, not an assumed normalizer quotient. -/
theorem positive_divisor_word (N : ℤ) (hN : 0<N) (hdiv : N∣210) :
    ∃ v : InertiaLabels318.V,N=(InertiaLabels318.divisor v:ℤ) := by
  have hle : N≤210 := Int.le_of_dvd (by norm_num) hdiv
  interval_cases N <;> norm_num at hdiv
  all_goals first
    | exact ⟨![0,0,0,0],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![1,0,0,0],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![0,1,0,0],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![0,0,1,0],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![1,1,0,0],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![0,0,0,1],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![1,0,1,0],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![1,0,0,1],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![0,1,1,0],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![0,1,0,1],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![1,1,1,0],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![0,0,1,1],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![1,1,0,1],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![1,0,1,1],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![0,1,1,1],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
    | exact ⟨![1,1,1,1],by norm_num [InertiaLabels318.divisor,Fin.prod_univ_succ,InertiaLabels318.primes]⟩
end PELNormalizerDivisorWords318
