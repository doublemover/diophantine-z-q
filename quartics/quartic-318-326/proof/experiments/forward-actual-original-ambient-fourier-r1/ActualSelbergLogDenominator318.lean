module
public import ActualOriginalEulerLogGrowth318
public section
noncomputable section
namespace ActualSelbergLogDenominator318
open scoped BigOperators
open ActualOriginalEulerLogGrowth318 ActualSelbergDenominator318 ActualSelbergDivisorWeights318
open ActualTruncatedSelbergEuler318 ActualOptimalSelbergBound318 ActualSelbergCoefficients318
open ActualRemovedSelbergSieve318
set_option maxHeartbeats 16000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Genuine log-power lower growth for the SAME strict integer-divisor
denominator at its CONSTRUCTED polynomial cutoff, uniformly in the
removed prime. The coefficient data precede every N and every removal. -/
theorem actual_denominator_log_growth (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) :
    ∃ C : ℝ,0<C ∧ ∀ N,2≤N → ∀ excluded : ℕ,
      C*(Real.log (N:ℝ))^(Fintype.card J)≤
        denominator κ γ j₀ N excluded (threshold J N) := by
  obtain ⟨C,hC,hbound⟩ := actual_full_euler_log_growth κ hκ γ hγ j₀ j₁ h0 h1
  refine ⟨C/4,by positivity,?_⟩
  intro N hN excluded
  have hh := div_le_div_of_nonneg_right (hbound N hN) (by norm_num : (0:ℝ)≤4)
  have hd := actual_denominator_lower κ hκ γ hγ j₀ j₁ h0 h1 N (by omega) excluded
  convert hh.trans hd using 1 <;> ring

/-- Actual produced natural Lambda coefficients and the original
weighted quadric sieve attain the logarithmic reciprocal main term.
No arbitrary weights, diagonal targets or density replacements remain. -/
theorem actual_optimizer_log_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) :
    ∃ C : ℝ,0<C ∧ ∀ N,2≤N → ∀ excluded : ℕ,
      ∀ S : Finset (QuadricCRTAssembly318.Quadric κ),
      (sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S).mainSum
        (BoundingSieve.lambdaSquared (coefficients κ γ j₀ N excluded (threshold J N)))≤
        C/(Real.log (N:ℝ))^(Fintype.card J) := by
  obtain ⟨C,hC,hbound⟩ := actual_denominator_log_growth κ hκ γ hγ j₀ j₁ h0 h1
  refine ⟨C⁻¹,inv_pos.mpr hC,?_⟩
  intro N hN excluded S
  have hlog : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hp : 0<C*(Real.log (N:ℝ))^(Fintype.card J) := by positivity
  have hi := one_div_le_one_div_of_le hp (hbound N hN excluded)
  rw [actual_main_sum κ hκ γ hγ j₀ j₁ h0 h1 N excluded _
    (threshold_gt_one N (by omega)) S]
  convert hi using 1 <;> simp only [one_div,mul_inv,div_eq_mul_inv]

/-- The final original finite-source weighted upper bound now has a
PRODUCED logarithmic main term and produced optimizer. The exact original
remainder is kept visible; no integer-point asymptotic is assumed. -/
theorem original_weighted_log_bound (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ)
    (hγ : Function.Injective γ) (j₀ j₁ : J) (h0 : γ j₀=0) (h1 : γ j₁= -κ) :
    ∃ C : ℝ,0<C ∧ ∀ N,2≤N → ∀ excluded : ℕ,
      ∀ S : Finset (QuadricCRTAssembly318.Quadric κ),
      (∑ v∈S,if Nat.Coprime (ActualTruncatedSelbergEuler318.product κ γ N excluded)
        (OriginalWeightedSelberg318.key κ γ v)
        then OriginalWeightedSelberg318.weight κ γ v else 0)≤
        C*(∑ v∈S,OriginalWeightedSelberg318.weight κ γ v)/
          (Real.log (N:ℝ))^(Fintype.card J)+
        (sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S).errSum
          (BoundingSieve.lambdaSquared (coefficients κ γ j₀ N excluded (threshold J N))) := by
  obtain ⟨C,hC,hbound⟩ := actual_optimizer_log_bound κ hκ γ hγ j₀ j₁ h0 h1
  refine ⟨C,hC,?_⟩
  intro N hN excluded S
  rw [←ActualRemovedSelbergSieve318.actual_sifted_sum κ hκ γ hγ j₀ j₁ h0 h1]
  have hh := @BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius
    (sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S)
    (BoundingSieve.lambdaSquared (coefficients κ γ j₀ N excluded (threshold J N)))
    (BoundingSieve.upperMoebius_lambdaSquared _
      (actual_coefficient_one κ hκ γ hγ j₀ j₁ h0 h1 N excluded _
        (threshold_gt_one N (by omega))))
  have hm : 0≤(sieve κ hκ γ hγ j₀ j₁ h0 h1 N excluded S).totalMass :=
    Finset.sum_nonneg (fun v _ => OriginalWeightedSelberg318.weight_nonneg κ γ v)
  have ht := mul_le_mul_of_nonneg_left (hbound N hN excluded S) hm
  have hu := hh.trans (add_le_add_right ht _)
  convert hu using 1 <;> dsimp only [sieve,OriginalWeightedSelberg318.sieve] <;> ring

end ActualSelbergLogDenominator318
