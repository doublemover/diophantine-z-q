module
public import ActualCharacterLogFactor318
public section
noncomputable section
namespace ActualCharacterFiniteLogControl318
open scoped BigOperators
open ActualModFourSieveCharacter318 ActualCharacterLogFactor318 ActualMovingBoundaryPrimeTail318
set_option maxHeartbeats 20000000

@[expose] def finiteEuler (σ : ℝ) (S : Finset ℕ) : ℝ :=
  ∏ p∈S,(1-realCharacter p*(p:ℝ)^(-σ))⁻¹
@[expose] def finiteLog (σ : ℝ) (S : Finset ℕ) : ℝ := ∑p∈S,logFactor σ p
@[expose] def shiftConstant : ℝ := 2*Real.log 4*(1+1/Real.log 2)
@[expose] def tailConstant : ℝ := 8*Real.log 4/Real.log 2

lemma finite_euler_pos (σ : ℝ) (hσ : 1≤σ) (S : Finset ℕ) (hS : ∀p∈S,p.Prime) :
    0<finiteEuler σ S := Finset.prod_pos (fun p hp =>
      inv_pos.mpr (actual_factor_positive σ hσ p (hS p hp)))
lemma actual_finite_log (σ : ℝ) (hσ : 1≤σ) (S : Finset ℕ) (hS : ∀p∈S,p.Prime) :
    Real.log (finiteEuler σ S)=finiteLog σ S := by
  rw [finiteEuler,Real.log_prod]
  · simp only [Real.log_inv,finiteLog,logFactor]
  · intro p hp
    exact inv_ne_zero (actual_factor_positive σ hσ p (hS p hp)).ne'

/-- Uniform logarithmic change of the ACTUAL finite Euler product
belowN, evaluated at sigma(N)=1+1/logN and at1. -/
theorem actual_finite_shift (N : ℕ) (hN : 1<N) (S : Finset ℕ)
    (hS : ∀p∈S,p.Prime ∧ p≤N) :
    |finiteLog 1 S-finiteLog (sigma N) S|≤shiftConstant := by
  have hd := (delta_pos N hN).le
  have hs : |finiteLog 1 S-finiteLog (sigma N) S|≤
      ∑p∈S,2*delta N*Real.log (p:ℝ)/(p:ℝ) := by
    unfold finiteLog
    rw [←Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun p hp => actual_log_factor_shift p (hS p hp).1 (delta N) hd))
  have he : (∑p∈S,2*delta N*Real.log (p:ℝ)/(p:ℝ))=
      2*delta N*∑p∈S,Real.log (p:ℝ)/(p:ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he] at hs
  have hm := ActualChebyshevLogMoment318.actual_prime_log_moment S N (by omega) hS
  have hu := mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) hd)
  have hlog : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast hN)
  have h2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have h4 : 0≤Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  have hlog2 : Real.log (2:ℝ)≤Real.log (N:ℝ) := Real.log_le_log (by norm_num)
    (by exact_mod_cast (show 2≤N by omega))
  have hi := one_div_le_one_div_of_le h2 hlog2
  have hbound : 2*delta N*(Real.log 4*(1+Real.log (N:ℝ)))≤shiftConstant := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add_left hi 1) (mul_nonneg (by norm_num) h4)
    unfold delta shiftConstant
    convert hh using 1 <;> field_simp [hlog.ne',h2.ne'] <;> ring
  exact hs.trans (hu.trans hbound)

/-- Uniform absolute logarithmic tail on ANY finite actual prime set
aboveN at the produced moving exponent. This is quantitative and does
not assert convergence of the prime product at exponent1. -/
theorem actual_finite_tail (N : ℕ) (hN : 1<N) (S : Finset ℕ)
    (hS : ∀p∈S,p.Prime ∧ N≤p) : |finiteLog (sigma N) S|≤tailConstant := by
  have hs : |finiteLog (sigma N) S|≤∑p∈S,2*(p:ℝ)^(-sigma N) :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun p hp => actual_log_factor_bound (sigma N)
        (sigma_gt_one N hN).le p (hS p hp).1))
  rw [←Finset.mul_sum] at hs
  have hu := mul_le_mul_of_nonneg_left (actual_moving_prime_tail N hN S hS) (by norm_num : (0:ℝ)≤2)
  exact hs.trans (by unfold tailConstant;convert hu using 1 <;> ring)

/-- These bounds control logarithms of the same POSITIVE actual Euler
products, not merely an independently defined additive prime sum. -/
theorem actual_euler_shift_and_tail (N : ℕ) (hN : 1<N) (A B : Finset ℕ)
    (hA : ∀p∈A,p.Prime ∧ p≤N) (hB : ∀p∈B,p.Prime ∧ N≤p) :
    |Real.log (finiteEuler 1 A)-Real.log (finiteEuler (sigma N) A)|≤shiftConstant ∧
      |Real.log (finiteEuler (sigma N) B)|≤tailConstant := by
  rw [actual_finite_log 1 le_rfl A (fun p hp => (hA p hp).1),
    actual_finite_log (sigma N) (sigma_gt_one N hN).le A (fun p hp => (hA p hp).1),
    actual_finite_log (sigma N) (sigma_gt_one N hN).le B (fun p hp => (hB p hp).1)]
  exact ⟨actual_finite_shift N hN A hA,actual_finite_tail N hN B hB⟩

end ActualCharacterFiniteLogControl318
