module
public import ActualOriginalResidueKernelBound318
public section
noncomputable section
namespace ActualOriginalUnitGaussBound318
open ActualOriginalQuadraticGauss318 ActualOriginalResidueKernelBound318
set_option maxHeartbeats 16000000

/-- Uniform quadratic Gauss bound for every unit numerator, arbitrary
linear frequency and nonzero modulus. The coefficient k need not be a unit;
the actual kernel count supplies the bad-prime/even-modulus constant2*k. -/
theorem actual_unit_gauss_square_bound (q k : ℕ) [NeZero q] (hk : 0 < k)
    (a b : ZMod q) (ha : IsUnit a) :
    ‖quadraticGauss q (a*(k : ZMod q)) b‖^2 ≤ (q : ℝ)*(2*(k : ℝ)) := by
  have hc : (kernelCard q (2*(a*(k : ZMod q))) : ℝ) ≤ 2*(k : ℝ) := by
    exact_mod_cast actual_unit_quadratic_kernel_bound q k hk a ha
  exact (actual_quadratic_gauss_square_bound q (a*(k : ZMod q)) b).trans
    (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg q))

lemma actual_unit_gauss_one_bound (q : ℕ) [NeZero q] (a b : ZMod q) (ha : IsUnit a) :
    ‖quadraticGauss q a b‖^2 ≤ 2*(q : ℝ) := by
  simpa only [Nat.cast_one,mul_one,mul_comm] using
    actual_unit_gauss_square_bound q 1 (by omega) a b ha

end ActualOriginalUnitGaussBound318
