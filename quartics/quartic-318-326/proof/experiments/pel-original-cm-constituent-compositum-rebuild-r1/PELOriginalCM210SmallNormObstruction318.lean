module
public import PELOriginalCM210NativeElementNorm318
public section
noncomputable section
namespace PELOriginalCM210SmallNormObstruction318
open PELOriginalCM210IntegralConjugation318
/-- Universal positive-definite norm obstruction, without bounding the input coordinates. -/
lemma small_norm (d:ℤ) (hd:d<210) (hns:∀r:ℤ,r^2≠d) (z:R) :
    z.re^2+210*z.im^2≠d := by
  intro h
  have hi : z.im^2<1 := by nlinarith [sq_nonneg z.re]
  have hi0 : z.im^2=0 := by have := sq_nonneg z.im; omega
  have him : z.im=0 := pow_eq_zero hi0
  apply hns z.re
  simpa [him] using h
@[expose] def divisor : Fin 14→ℕ := ![2,3,5,6,7,10,14,15,21,30,35,42,70,105]
lemma divisor_properties (i:Fin 14) : 0<divisor i ∧ divisor i<210 ∧ (divisor i:ℤ)∣210 := by
  fin_cases i <;> norm_num [divisor]
lemma divisor_nonsquare (i:Fin 14) (r:ℤ) : r^2≠(divisor i:ℤ) := by
  intro h
  have hd : (divisor i:ℤ)≤105 := by fin_cases i <;> norm_num [divisor]
  have hr : -10≤r ∧ r≤10 := by
    constructor <;> nlinarith [sq_nonneg (r-11),sq_nonneg (r+11)]
  interval_cases r <;> fin_cases i <;> norm_num [divisor] at h
lemma no_divisor_norm (i:Fin 14) (z:R) : z.re^2+210*z.im^2≠(divisor i:ℤ) :=
  small_norm _ (by exact_mod_cast (divisor_properties i).2.1) (divisor_nonsquare i) z
end PELOriginalCM210SmallNormObstruction318
