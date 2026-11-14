module
public import ActualSelbergPolynomialWeights318
public section
noncomputable section
namespace ActualSelbergRemainderBudget318
open scoped BigOperators
open ActualTruncatedSelbergEuler318 ActualRemovedSelbergSieve318 ActualSelbergCoefficients318
open ActualSelbergPolynomialWeights318
set_option maxHeartbeats 24000000
variable {J : Type*} [Fintype J] [DecidableEq J]

lemma actual_lambda_squared_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N excluded : ℕ) (z : ℝ) (hz : 1<z) (d : ℕ) :
    |BoundingSieve.lambdaSquared (coefficients κ γ j₀ N excluded z) d|≤(Nat.ceil z:ℝ)^10 := by
  let λ := coefficients κ γ j₀ N excluded z
  have hL := actual_coefficient_l1 κ hκ γ hγ j₀ j₁ h0 h1 N excluded z hz d.divisors
  have hL0 : 0≤∑ a∈d.divisors,|λ a| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc
    _ ≤ ∑ a∈d.divisors,|∑ b∈d.divisors,if d=Nat.lcm a b then λ a*λ b else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a∈d.divisors,∑ b∈d.divisors,|if d=Nat.lcm a b then λ a*λ b else 0| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a∈d.divisors,∑ b∈d.divisors,|λ a|*|λ b| := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      split_ifs
      · rw [abs_mul]
      · simp only [abs_zero]
        positivity
    _ = (∑ a∈d.divisors,|λ a|)^2 := by
      simp only [sq,Finset.sum_mul,Finset.mul_sum]
    _ ≤ ((Nat.ceil z:ℝ)^5)^2 := pow_le_pow_left₀ hL0 hL 2
    _ = (Nat.ceil z:ℝ)^10 := by ring

/-- The ACTUAL Lambda-squared coefficients have strict support d<z²,
because any contributing lcm is at most the product of two moduli<z. -/
lemma actual_lambda_squared_support (κ : ℤ) (γ : J → ℤ) (j₀ : J) (N excluded : ℕ)
    (z : ℝ) (hz : 0<z) (d : ℕ) (hd : z^2≤(d:ℝ)) :
    BoundingSieve.lambdaSquared (coefficients κ γ j₀ N excluded z) d=0 := by
  classical
  unfold BoundingSieve.lambdaSquared
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  by_cases hab : d=Nat.lcm a b
  · rw [if_pos hab]
    by_cases ha : z≤(a:ℝ)
    · rw [actual_coefficient_support κ γ j₀ N excluded z a ha,zero_mul]
    · by_cases hb : z≤(b:ℝ)
      · rw [actual_coefficient_support κ γ j₀ N excluded z b hb,mul_zero]
      · have hla : (a:ℝ)<z := lt_of_not_ge ha
        have hlb : (b:ℝ)<z := lt_of_not_ge hb
        have hmul : (a:ℝ)*(b:ℝ)<z^2 := by
          calc
            _ ≤ (a:ℝ)*z := mul_le_mul_of_nonneg_left hlb.le (Nat.cast_nonneg a)
            _ < z*z := mul_lt_mul_of_pos_right hla hz
            _ = z^2 := by ring
        have hlcm : (d:ℝ)≤(a:ℝ)*(b:ℝ) := by
          rw [hab]
          exact_mod_cast Nat.lcm_le_mul a b
        exact False.elim (not_lt_of_ge hd (hlcm.trans_lt hmul))
  · rw [if_neg hab]

/-- A concrete finite operator budget for the ORIGINAL divisor
remainders. The sum contains those actual remainders; it is not a
finite-CRT replacement for the missing integer-point asymptotic. -/
@[expose] def remainderBudget (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ) (z : ℝ)
    (S : Finset (QuadricCRTAssembly318.Quadric κ)) : ℝ :=
  (Nat.ceil z:ℝ)^10*∑ d∈Finset.range (Nat.ceil (z^2)),
    |(sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S).rem d|

theorem actual_error_operator_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N excluded : ℕ) (z : ℝ) (hz : 1<z)
    (S : Finset (QuadricCRTAssembly318.Quadric κ)) :
    (sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S).errSum
      (BoundingSieve.lambdaSquared (coefficients κ γ j₀ N excluded z))≤
      remainderBudget κ hκ γ hγ j₀ j₁ h0 h1 N excluded z S := by
  classical
  let s := sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S
  let T := s.prodPrimes.divisors.filter (fun d => (d:ℝ)<z^2)
  let μ := BoundingSieve.lambdaSquared (coefficients κ γ j₀ N excluded z)
  have he : s.errSum μ=∑ d∈T,|μ d|*|s.rem d| := by
    rw [BoundingSieve.errSum,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : (d:ℝ)<z^2
    · rw [if_pos hd]
    · rw [if_neg hd,actual_lambda_squared_support κ γ j₀ N excluded z (by linarith) d (le_of_not_gt hd)]
      simp
  have hsub : T⊆Finset.range (Nat.ceil (z^2)) := by
    intro d hd
    have hlt := (Finset.mem_filter.mp hd).2
    exact Finset.mem_range.mpr (by exact_mod_cast hlt.trans_le (Nat.le_ceil (z^2)))
  calc
    _ = ∑ d∈T,|μ d|*|s.rem d| := he
    _ ≤ ∑ d∈T,(Nat.ceil z:ℝ)^10*|s.rem d| := Finset.sum_le_sum (fun d _ =>
      mul_le_mul_of_nonneg_right
        (actual_lambda_squared_bound κ hκ γ hγ j₀ j₁ h0 h1 N excluded z hz d) (abs_nonneg _))
    _ = (Nat.ceil z:ℝ)^10*∑ d∈T,|s.rem d| := (Finset.mul_sum _ _ _).symm
    _ ≤ (Nat.ceil z:ℝ)^10*∑ d∈Finset.range (Nat.ceil (z^2)),|s.rem d| :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)) (by positivity)
    _ = _ := rfl

/-- Uniform numerical remainder estimates, when proved for the actual
original point count, can be consumed with a fully explicit polynomial
loss. This lemma does NOT supply such an estimate. -/
theorem budget_of_uniform_remainder (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N excluded : ℕ) (z E : ℝ) (S : Finset (QuadricCRTAssembly318.Quadric κ))
    (hE : ∀ d∈Finset.range (Nat.ceil (z^2)),
      |(sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S).rem d|≤E) :
    remainderBudget κ hκ γ hγ j₀ j₁ h0 h1 N excluded z S≤
      (Nat.ceil z:ℝ)^10*(Nat.ceil (z^2):ℝ)*E := by
  unfold remainderBudget
  have hs := Finset.sum_le_sum hE
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0≤(Nat.ceil z:ℝ)^10)
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_assoc] using hh

end ActualSelbergRemainderBudget318
