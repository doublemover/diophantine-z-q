module
public import ActualOriginalReciprocalLogBudget318
public section
noncomputable section
namespace ActualOriginalCompleteLogKernel318
open ActualOriginalReciprocalLogBudget318 ActualOriginalCompleteTwoAxisWeyl318
open ActualOriginalScaledDisplacementBlockCount318

/-- Complete even-displacement kernel, with the actual finite bin sum
removed by a proved harmonic logarithm estimate. -/
theorem actual_complete_log_kernel (a q H : ℤ) (t N : ℝ)
    (hq : 0<q) (ha : IsCoprime q a) (hH : 0≤H)
    (ht : |t-(a : ℝ)/(q : ℝ)|≤1/(q : ℝ)^2) (hN : 0≤N) :
    completeEvenKernel H N t≤(16*(H : ℝ)/(q : ℝ)+2)*logBlockBudget N q := by
  apply (actual_scaled_even_displacement_budget a q H t N hq ha hH ht hN).trans
  apply mul_le_mul_of_nonneg_left (actual_reciprocal_block_log N q hq)
  have hHi : (0 : ℝ)≤H := by exact_mod_cast hH
  have hqi : (0 : ℝ)≤q := by exact_mod_cast (le_of_lt hq)
  positivity

end ActualOriginalCompleteLogKernel318
