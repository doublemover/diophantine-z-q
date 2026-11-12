module
public import ActualOriginalBinHarmonicBudget318
public import Mathlib.NumberTheory.Harmonic.Bounds
public section
noncomputable section
namespace ActualOriginalReciprocalLogBudget318
open ActualOriginalBinHarmonicBudget318 ActualOriginalCompleteFrequencyBudget318
open scoped BigOperators

/-- Exact identification of the integer positive reciprocal sum with
the native rational harmonic number, then real scalar transport. -/
lemma actual_positive_sum_harmonic (q : ℤ) (hq : 0<q) :
    positiveReciprocalSum q=(harmonic q.toNat : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  symm
  apply Finset.sum_bij (fun n _ => (n : ℤ))
  · intro n hn
    have hh := Finset.mem_Icc.mp hn
    apply Finset.mem_Icc.mpr
    omega
  · intro n hn m hm he
    omega
  · intro b hb
    have hh := Finset.mem_Icc.mp hb
    refine ⟨b.toNat,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩
  · intro n hn
    simp only [Int.cast_natCast]

lemma actual_positive_sum_log (q : ℤ) (hq : 0<q) :
    positiveReciprocalSum q≤1+Real.log (q : ℝ) := by
  rw [actual_positive_sum_harmonic q hq]
  have hcast : (q.toNat : ℝ)=(q : ℝ) := by exact_mod_cast Int.toNat_of_nonneg (le_of_lt hq)
  simpa only [hcast] using harmonic_le_one_add_log q.toNat

@[expose] def logBlockBudget (N : ℝ) (q : ℤ) : ℝ :=
  2*N+2*(q : ℝ)*(1+Real.log (q : ℝ))

/-- The previously explicit bin-sum budget now has a proved logarithmic
upper bound, retaining BOTH full-length near-resonance bins. -/
theorem actual_reciprocal_block_log (N : ℝ) (q : ℤ) (hq : 0<q) :
    reciprocalBlockBudget N q≤logBlockBudget N q := by
  apply (actual_reciprocal_block_harmonic N q hq).trans
  unfold logBlockBudget
  exact add_le_add_left (mul_le_mul_of_nonneg_left (actual_positive_sum_log q hq)
    (by have : (0 : ℝ)≤q := by exact_mod_cast (le_of_lt hq); positivity)) (2*N)

lemma actual_log_block_budget_nonneg (N : ℝ) (q : ℤ) (hN : 0≤N) (hq : 0<q) :
    0≤logBlockBudget N q :=
  (actual_reciprocal_block_budget_nonneg N q hN hq).trans (actual_reciprocal_block_log N q hq)

end ActualOriginalReciprocalLogBudget318
