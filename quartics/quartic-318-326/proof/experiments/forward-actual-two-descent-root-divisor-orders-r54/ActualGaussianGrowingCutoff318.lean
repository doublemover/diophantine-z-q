module
public import ActualGaussianUniformPowerTail318
public section
noncomputable section
namespace ActualGaussianGrowingCutoff318
open scoped BigOperators
open ActualGaussianUniformPowerTail318 ActualGaussianFullSourceTail318 OriginalWeightedSelberg318
set_option maxHeartbeats 12000000
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The actual integer cutoff includes the fixed coefficient primes and
rounds B^(1/100) UP. It is selected from B and kappa only, before primes
or individual source points, and has no unproved eventual threshold. -/
@[expose] def cutoff (κ : ℤ) (B : ℕ) : ℕ :=
  max κ.natAbs (max 3 (Nat.ceil ((B:ℝ)^((1:ℝ)/100))))
lemma cutoff_three (κ : ℤ) (B : ℕ) : 3≤cutoff κ B :=
  (le_max_left _ _).trans (le_max_right _ _)
lemma cutoff_coefficient (κ : ℤ) (B : ℕ) : κ.natAbs≤cutoff κ B :=
  le_max_left _ _
lemma cutoff_power (κ : ℤ) (B : ℕ) : (B:ℝ)^((1:ℝ)/100)≤(cutoff κ B:ℝ) := by
  have hh : Nat.ceil ((B:ℝ)^((1:ℝ)/100))≤cutoff κ B :=
    (le_max_right _ _).trans (le_max_right _ _)
  exact (Nat.le_ceil _).trans (by exact_mod_cast hh)

@[expose] def growingConstant (κ : ℤ) (γ : J → ℤ) : ℝ :=
  mainConstant κ γ ((1:ℝ)/1000)+errorConstant κ γ ((1:ℝ)/1000)

/-- The full ORIGINAL weighted Gaussian source has a concrete power-saving
at the constructed growing cutoff: exponent3-1/200. It includes R=0,
both-label primes, both genuine charts, every generator and every large
prime. This remains an upper bound, not a lower-bound/existence theorem. -/
theorem actual_full_growing_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) :
    mass B κ (cutoff κ B) γ≤growingConstant κ γ*(B:ℝ)^(3-(1:ℝ)/200) := by
  have hb : (1:ℝ)≤B := by exact_mod_cast hB
  have hbpos : (0:ℝ)<B := zero_lt_one.trans_le hb
  obtain ⟨hm,he⟩ := constants_nonneg κ γ ((1:ℝ)/1000) (by norm_num)
  have hsource := actual_uniform_power_tail B hB κ hκ (cutoff κ B)
    (cutoff_three κ B) γ ((1:ℝ)/1000) (by norm_num)
  have hdiv := div_le_div_of_nonneg_left
    (mul_nonneg hm (Real.rpow_nonneg hbpos.le _))
    (Real.rpow_pos_of_pos hbpos ((1:ℝ)/100)) (cutoff_power κ B)
  have hmain : mainConstant κ γ ((1:ℝ)/1000)*(B:ℝ)^(3+(1:ℝ)/1000)/
      (cutoff κ B:ℝ)≤
      mainConstant κ γ ((1:ℝ)/1000)*(B:ℝ)^((2991:ℝ)/1000) := by
    exact hdiv.trans_eq (by
      rw [show (2991:ℝ)/1000=(3+(1:ℝ)/1000)-(1:ℝ)/100 by norm_num,Real.rpow_sub hbpos]
      ring)
  have hp := Real.rpow_le_rpow_of_exponent_le hb
    (by norm_num : (2991:ℝ)/1000≤3-(1:ℝ)/200)
  have hq := Real.rpow_le_rpow_of_exponent_le hb
    (by norm_num : (11:ℝ)/4+(1:ℝ)/1000≤3-(1:ℝ)/200)
  have hm' := mul_le_mul_of_nonneg_left hp hm
  have he' := mul_le_mul_of_nonneg_left hq he
  dsimp [growingConstant]
  nlinarith only [hsource,hmain,hm',he']

/-- Actual all-prime source mass at the constructed cutoff. The original
coefficient-prime exclusion is absent from this counted set. -/
@[expose] def allPrimeMass (B : ℕ) (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) : ℝ := by
  classical
  letI : Fintype (FullSource B κ (cutoff κ B)) := Fintype.ofFinite _
  letI : Fintype (AllPrimeSource B κ (cutoff κ B)) :=
    Fintype.ofEquiv (FullSource B κ (cutoff κ B))
      (allPrimeEquiv B κ hκ (cutoff κ B) (cutoff_coefficient κ B)).symm
  exact ∑ v : AllPrimeSource B κ (cutoff κ B),weight κ γ v.1

lemma allPrimeMass_eq (B : ℕ) (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) :
    allPrimeMass B κ hκ γ=mass B κ (cutoff κ B) γ := by
  classical
  letI : Fintype (FullSource B κ (cutoff κ B)) := Fintype.ofFinite _
  letI : Fintype (AllPrimeSource B κ (cutoff κ B)) :=
    Fintype.ofEquiv (FullSource B κ (cutoff κ B))
      (allPrimeEquiv B κ hκ (cutoff κ B) (cutoff_coefficient κ B)).symm
  exact Equiv.sum_comp (allPrimeEquiv B κ hκ (cutoff κ B) (cutoff_coefficient κ B))
    (fun v => weight κ γ v.1)

theorem actual_all_prime_growing_tail (B : ℕ) (hB : 1≤B) (κ : ℤ) (hκ : κ≠0) (γ : J → ℤ) :
    allPrimeMass B κ hκ γ≤growingConstant κ γ*(B:ℝ)^(3-(1:ℝ)/200) := by
  rw [allPrimeMass_eq]
  exact actual_full_growing_tail B hB κ hκ γ

end ActualGaussianGrowingCutoff318
