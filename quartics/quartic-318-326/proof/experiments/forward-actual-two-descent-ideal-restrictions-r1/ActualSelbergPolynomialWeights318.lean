module
public import ActualSievePolynomialDensity318
public section
noncomputable section
namespace ActualSelbergPolynomialWeights318
open scoped BigOperators
open ActualSieveMultiplicativeDensity318 ActualTruncatedSelbergEuler318 ActualSelbergDivisorChoices318
open ActualRemovedSelbergSieve318 ActualSelbergCoefficients318 ActualSievePolynomialDensity318
set_option maxHeartbeats 20000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Every actually produced natural coefficient has a uniform
polynomial bound, with no unproved first-order density lower bound. -/
theorem actual_coefficient_polynomial_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N excluded : ℕ) (z : ℝ) (hz : 1<z) (d : ℕ) :
    |coefficients κ γ j₀ N excluded z d|≤(d:ℝ)^4 := by
  classical
  by_cases hd : d∣product κ γ N excluded
  · let a := bits κ γ N excluded d
    have ha : modulus κ γ N excluded a=d := actual_divisor_reconstruction κ γ N excluded d hd
    have hν := actual_modulus_nu_pos κ hκ γ hγ j₀ j₁ h0 h1 N excluded a
    have hh := FiniteMobiusCoefficientBound318.actual_coefficient_abs
      (choiceNu κ γ j₀ N excluded) (choiceTerm κ γ j₀ N excluded) (choiceCut κ γ N excluded z)
      (actual_modulus_nu_pos κ hκ γ hγ j₀ j₁ h0 h1 N excluded)
      (fun b => (actual_modulus_terms_pos κ hκ γ hγ j₀ j₁ h0 h1 N excluded b).le)
      (actual_mass_pos κ hκ γ hγ j₀ j₁ h0 h1 N excluded z hz) a
    rw [←coefficient_at_modulus,choiceNu,ha] at hh
    rw [ha] at hν
    have hlow := actual_divisor_polynomial_lower κ hκ γ hγ j₀ j₁ h0 h1 N excluded d hd
    have hrec : 1/nu κ γ j₀ d≤(d:ℝ)^4 := by
      apply (div_le_iff₀ hν).mpr
      simpa only [mul_comm] using hlow
    exact hh.trans hrec
  · simp only [coefficients,if_neg hd,abs_zero]
    positivity

/-- Uniform L1 bound over ANY finite set of actual integer moduli.
The strict cutoff is used before counting, so the number of prime
divisors of the retained product never enters the bound. -/
theorem actual_coefficient_l1 (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N excluded : ℕ) (z : ℝ) (hz : 1<z) (T : Finset ℕ) :
    (∑ d∈T,|coefficients κ γ j₀ N excluded z d|)≤(Nat.ceil z:ℝ)^5 := by
  classical
  let C := Nat.ceil z
  let f := fun d => |coefficients κ γ j₀ N excluded z d|
  have he : (∑ d∈T,f d)=∑ d∈T.filter (fun d => (d:ℝ)<z),f d := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : (d:ℝ)<z
    · rw [if_pos hd]
    · rw [if_neg hd]
      simpa only [abs_zero] using congrArg abs
        (actual_coefficient_support κ γ j₀ N excluded z d (le_of_not_gt hd))
  have hsub : T.filter (fun d => (d:ℝ)<z)⊆Finset.range C := by
    intro d hd
    have hh := (Finset.mem_filter.mp hd).2
    have hc : (d:ℝ)<C := hh.trans_le (Nat.le_ceil z)
    exact Finset.mem_range.mpr (by exact_mod_cast hc)
  calc
    _ = ∑ d∈T.filter (fun d => (d:ℝ)<z),f d := he
    _ ≤ ∑ d∈Finset.range C,f d := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun d _ _ => abs_nonneg _)
    _ ≤ ∑ _∈Finset.range C,(C:ℝ)^4 := by
      apply Finset.sum_le_sum
      intro d hd
      have h := actual_coefficient_polynomial_bound κ hκ γ hγ j₀ j₁ h0 h1 N excluded z hz d
      have hdc : (d:ℝ)≤C := by exact_mod_cast (Finset.mem_range.mp hd).le
      exact h.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hdc 4)
    _ = (C:ℝ)^5 := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul];ring

end ActualSelbergPolynomialWeights318
