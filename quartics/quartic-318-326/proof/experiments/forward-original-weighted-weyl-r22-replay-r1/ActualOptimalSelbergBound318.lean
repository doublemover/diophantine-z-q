module
public import ActualSelbergCoefficients318
public section
noncomputable section
namespace ActualOptimalSelbergBound318
open scoped BigOperators
open ActualSieveMultiplicativeDensity318 ActualSievePrimeMoment318 ActualTruncatedSelbergEuler318
open ActualSelbergDivisorChoices318 ActualSelbergDivisorWeights318 ActualRemovedSelbergSieve318
open ActualSelbergCoefficients318 ActualRemovedEulerFactor318
set_option maxHeartbeats 24000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Exact diagonal energy of the CONSTRUCTED coefficients on the
actual removed-prime sieve. The entire integer-divisor quadratic form
is used, not merely a formal diagonal target. -/
theorem actual_main_sum (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N excluded : ℕ) (z : ℝ) (hz : 1<z)
    (S : Finset (QuadricCRTAssembly318.Quadric κ)) :
    (sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S).mainSum
      (BoundingSieve.lambdaSquared (coefficients κ γ j₀ N excluded z))=
      (denominator κ γ j₀ N excluded z)⁻¹ := by
  classical
  let s := sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  change (∑ l∈(product κ γ N excluded).divisors,(terms κ γ j₀ l)⁻¹*
    (∑ d∈(product κ γ N excluded).divisors,
      if l∣d then nu κ γ j₀ d*coefficients κ γ j₀ N excluded z d else 0)^2)=_
  have he := Equiv.sum_comp (divisorEquiv κ γ N excluded)
    (fun l : ↥(product κ γ N excluded).divisors => (terms κ γ j₀ l.1)⁻¹*
      (∑ d∈(product κ γ N excluded).divisors,
        if l.1∣d then nu κ γ j₀ d*coefficients κ γ j₀ N excluded z d else 0)^2)
  rw [Finset.sum_coe_sort] at he
  rw [←he]
  change (∑ a : PrimeIndex κ γ N excluded → Bool,
    (choiceTerm κ γ j₀ N excluded a)⁻¹*
      (∑ d∈(product κ γ N excluded).divisors,
        if modulus κ γ N excluded a∣d then nu κ γ j₀ d*coefficients κ γ j₀ N excluded z d else 0)^2)=_
  simp_rw [actual_diagonal_coordinate κ hκ γ hγ j₀ j₁ h0 h1]
  rw [FiniteSelbergMinimizer318.target_energy
    (choiceTerm κ γ j₀ N excluded) (choiceCut κ γ N excluded z)
    (fun a => (actual_modulus_terms_pos κ hκ γ hγ j₀ j₁ h0 h1 N excluded a).ne')
    (actual_mass_pos κ hκ γ hγ j₀ j₁ h0 h1 N excluded z hz).ne']
  rw [actual_mass_identity κ hκ γ hγ j₀ j₁ h0 h1]

/-- Genuine optimized original weighted-point upper bound. The error
is still the EXACT original divisor remainder; no congruence-count
asymptotic or prime production is smuggled into optimization. -/
theorem actual_weighted_upper_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N excluded : ℕ) (z : ℝ) (hz : 1<z)
    (S : Finset (QuadricCRTAssembly318.Quadric κ)) :
    (∑ v∈S,if Nat.Coprime (product κ γ N excluded) (OriginalWeightedSelberg318.key κ γ v)
      then OriginalWeightedSelberg318.weight κ γ v else 0)≤
      (sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S).totalMass/
        denominator κ γ j₀ N excluded z+
      (sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S).errSum
        (BoundingSieve.lambdaSquared (coefficients κ γ j₀ N excluded z)) := by
  rw [←actual_sifted_sum κ hκ γ hγ j₀ j₁ h0 h1]
  have hh := @BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
    (sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S)
    (BoundingSieve.lambdaSquared (coefficients κ γ j₀ N excluded z))
    (BoundingSieve.upperMoebius_lambdaSquared _
      (actual_coefficient_one κ hκ γ hγ j₀ j₁ h0 h1 N excluded z hz))
  rw [actual_main_sum κ hκ γ hγ j₀ j₁ h0 h1 N excluded z hz S] at hh
  simpa only [div_eq_mul_inv] using hh

lemma threshold_gt_one (N : ℕ) (hN : 1≤N) : 1<threshold J N := by
  have hlog : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have h4 : 0≤Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  have hc := (momentConstant_pos (J := J)).le
  have hm : 0≤momentBound J N := by dsimp [momentBound];positivity
  have hL : 0<logThreshold J N := by dsimp [logThreshold];linarith
  exact Real.one_lt_exp_iff.mpr hL

lemma full_euler_pos (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) (hγ : Function.Injective γ)
    (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) (N : ℕ) : 0<fullEuler κ γ j₀ N := by
  apply Finset.prod_pos
  intro p hp
  have hh := (actual_local_upper κ hκ γ hγ j₀ j₁ h0 h1 p (selected_eligible κ γ N p hp)).2
  apply div_pos (by norm_num)
  linarith

/-- Produced polynomial level and produced Lambda coefficients give
an explicit reciprocal-Euler main term, uniformly in the removed prime. -/
theorem actual_produced_main_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ)
    (N : ℕ) (hN : 1≤N) (excluded : ℕ) (S : Finset (QuadricCRTAssembly318.Quadric κ)) :
    (sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S).mainSum
      (BoundingSieve.lambdaSquared (coefficients κ γ j₀ N excluded (threshold J N)))≤
      4/fullEuler κ γ j₀ N := by
  rw [actual_main_sum κ hκ γ hγ j₀ j₁ h0 h1 N excluded _ (threshold_gt_one N hN) S]
  have hD := ActualSelbergDenominator318.actual_denominator_lower κ hκ γ hγ j₀ j₁ h0 h1 N hN excluded
  have hE := full_euler_pos κ hκ γ hγ j₀ j₁ h0 h1 N
  have hp : 0<fullEuler κ γ j₀ N/4 := by positivity
  have hi := one_div_le_one_div_of_le hp hD
  convert hi using 1 <;> field_simp

end ActualOptimalSelbergBound318
