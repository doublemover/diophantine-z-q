module
public import SquareReflection318
public import PELOriginalCM210NativeSignature318
public section
noncomputable section
namespace PELOriginalCM210PrimeDiscriminantData318
@[expose] def radicand : Fin 4→ℚ := ![-2,-3,5,-7]
@[expose] def primeDiscriminant : Fin 4→ℤ := ![-8,-3,5,-7]
lemma radicand_product : ((radicand 0*radicand 1)*radicand 2)*radicand 3=-210 := by
  norm_num [radicand]
lemma discriminant_product :
    ((primeDiscriminant 0*primeDiscriminant 1)*primeDiscriminant 2)*primeDiscriminant 3=-840 := by
  norm_num [primeDiscriminant]
@[expose] def positiveClass : Fin 7→ℤ := ![5,6,14,21,30,70,105]
@[expose] def negativeClass : Fin 8→ℚ := ![-2,-3,-7,-10,-15,-35,-42,-210]
lemma positive_not_square (i:Fin 7) : ¬IsSquare (positiveClass i:ℚ) := by
  intro hs
  have hz : IsSquare (positiveClass i) :=
    (SquareReflection318.fraction_square_iff (R:=ℤ) (K:=ℚ) _).mp (by simpa using hs)
  obtain ⟨z,hz⟩ := hz
  have hb : positiveClass i≤105 := by fin_cases i <;> norm_num [positiveClass]
  have hr : -10≤z ∧ z≤10 := by
    constructor <;> nlinarith [sq_nonneg (z-11),sq_nonneg (z+11)]
  interval_cases z <;> fin_cases i <;> norm_num [positiveClass] at hz
lemma negative_not_square (i:Fin 8) : ¬IsSquare (negativeClass i) := by
  rintro ⟨z,hz⟩
  have hn : negativeClass i<0 := by fin_cases i <;> norm_num [negativeClass]
  nlinarith [sq_nonneg z]
end PELOriginalCM210PrimeDiscriminantData318
