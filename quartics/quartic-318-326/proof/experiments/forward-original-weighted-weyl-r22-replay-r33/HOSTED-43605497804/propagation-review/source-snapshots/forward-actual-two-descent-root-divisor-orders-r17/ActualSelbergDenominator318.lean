module
public import ActualRemovedEulerFactor318
public section
noncomputable section
namespace ActualSelbergDenominator318
open scoped BigOperators
open ActualSieveMultiplicativeDensity318 ActualSievePrimeMoment318 ActualTruncatedSelbergEuler318
open ActualSelbergDivisorWeights318 ActualRemovedEulerFactor318
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The actual strict-divisor Selberg denominator, uniformly after one
prime is removed, retains at least one quarter of the FULL original
Euler product at a constructed polynomial-scale cutoff. -/
theorem actual_denominator_lower (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N : ℕ) (hN : 1≤N) (excluded : ℕ) :
    fullEuler κ γ j₀ N/4≤denominator κ γ j₀ N excluded (threshold J N) := by
  rw [actual_denominator_eq_truncated κ hκ γ hγ j₀ j₁ h0 h1]
  have ht := actual_half_euler_truncation κ hκ γ hγ j₀ j₁ h0 h1 N hN excluded
  have he := actual_removed_factor κ hκ γ hγ j₀ j₁ h0 h1 N excluded
  linarith

/-- Literal original-source consumer: the summand is exactly Mathlib's
selbergTerms on the already constructed original weighted quadric sieve.
No arbitrary replacement density or source-dependent Euler factor is
allowed. The prime removal changes only the displayed divisor product. -/
theorem original_weighted_sieve_denominator (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N : ℕ) (hN : 1≤N) (excluded : ℕ)
    (S : Finset (QuadricCRTAssembly318.Quadric κ)) :
    fullEuler κ γ j₀ N/4≤
      ∑ d∈(product κ γ N excluded).divisors,
        if (d:ℝ)<threshold J N then
          (OriginalWeightedSelberg318.sieve κ hκ γ hγ j₀ j₁ h0 h1 N S).selbergTerms d else 0 := by
  have hh := actual_denominator_lower κ hκ γ hγ j₀ j₁ h0 h1 N hN excluded
  simpa only [denominator,terms_eq_original κ hκ γ hγ j₀ j₁ h0 h1 N S] using hh

/-- The full cutoff is chosen from the ORIGINAL coefficient count and
N before any divisor, removed prime, or actual finite source is chosen. -/
theorem original_polynomial_cutoff (N : ℕ) (hN : 1≤N) :
    threshold J N=Real.exp (1+2*momentConstant J*Real.log 4)*
      (N:ℝ)^(2*momentConstant J*Real.log 4) := threshold_polynomial N hN

end ActualSelbergDenominator318
