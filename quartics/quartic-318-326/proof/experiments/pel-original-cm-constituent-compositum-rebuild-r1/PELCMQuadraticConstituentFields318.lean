module
public import PELCMQuadraticNativeIntegerOrder318
public import PELOriginalCM210PrimeDiscriminantData318
public section
noncomputable section
namespace PELCMQuadraticConstituentFields318
open PELCMQuadraticIntegralTraceData318
@[expose] def a : Fin 4→ℤ := ![-2,-1,1,-2]
@[expose] def b : Fin 4→ℤ := ![0,1,1,1]
@[expose] def discriminant : Fin 4→ℤ := ![-8,-3,5,-7]
instance noRoot (i:Fin 4) : Fact (∀x:ℚ,x^2≠(a i:ℚ)+(b i:ℚ)*x) :=
  ⟨by
    intro x he
    fin_cases i
    · norm_num [a,b] at he
      nlinarith [sq_nonneg x]
    · norm_num [a,b] at he
      nlinarith [sq_nonneg (2*x-1)]
    · norm_num [a,b] at he
      apply PELOriginalCM210PrimeDiscriminantData318.positive_not_square 0
      refine ⟨2*x-1,?_⟩
      change (5:ℚ)=(2*x-1)*(2*x-1)
      linear_combination -4*he
    · norm_num [a,b] at he
      nlinarith [sq_nonneg (2*x-1)]⟩
abbrev Field (i:Fin 4) := F (a i) (b i)
abbrev Integers (i:Fin 4) := NumberField.RingOfIntegers (Field i)
lemma coefficient_discriminant (i:Fin 4) : D (a i) (b i)=discriminant i := by
  fin_cases i <;> norm_num [D,a,b,discriminant]
end PELCMQuadraticConstituentFields318
