module
public import ActualOriginalFiniteBoxProduct318
public section
noncomputable section
namespace ActualOriginalLinearIntervalCancellation318
open scoped BigOperators

/-- A genuine finite interval with arbitrary integer starting point.
The frequency c may be zero, or resonant at the specified circle point. -/
@[expose] def linearIntervalSum (c m : ℤ) (N : ℕ)
    (θ : AddCircle (1 : ℝ)) : ℂ :=
  ∑ j ∈ Finset.range N, fourier (c*(m+(j : ℤ))) θ

lemma actual_interval_phase_power (c m : ℤ) (j : ℕ)
    (θ : AddCircle (1 : ℝ)) :
    fourier (c*(m+(j : ℤ))) θ = fourier (c*m) θ*(fourier c θ)^j := by
  induction j with
  | zero => simp only [Nat.cast_zero,add_zero,pow_zero,mul_one]
  | succ j ih =>
    have he : c*(m+((j+1 : ℕ) : ℤ)) = c*(m+(j : ℤ))+c := by push_cast; ring
    rw [he,fourier_add,ih,pow_succ,mul_assoc]

lemma actual_linear_interval_geometric (c m : ℤ) (N : ℕ)
    (θ : AddCircle (1 : ℝ)) :
    linearIntervalSum c m N θ = fourier (c*m) θ*
      ∑ j ∈ Finset.range N, (fourier c θ)^j := by
  simp only [linearIntervalSum,actual_interval_phase_power,Finset.mul_sum]

/-- Telescoping is proved also at z=1. Division is deferred until the
nonresonant case, so no zero denominator is silently removed. -/
lemma actual_finite_geometric_telescoping (z : ℂ) (N : ℕ) :
    (z-1)*(∑ j ∈ Finset.range N, z^j) = z^N-1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,mul_add,ih,pow_succ]
    ring

lemma actual_linear_interval_length_bound (c m : ℤ) (N : ℕ)
    (θ : AddCircle (1 : ℝ)) : ‖linearIntervalSum c m N θ‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, ‖fourier (c*(m+(j : ℤ))) θ‖ := norm_sum_le _ _
    _ = _ := by
      have hu (j : ℕ) : ‖fourier (c*(m+(j : ℤ))) θ‖ = 1 := Circle.norm_coe _
      simp only [hu,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]

/-- The genuine nonresonant linear cancellation bound. Together with
the length bound this produces min(N,2/|e(c theta)-1|), not an assumed
black-box Weyl estimate. -/
theorem actual_linear_interval_cancellation (c m : ℤ) (N : ℕ)
    (θ : AddCircle (1 : ℝ)) (hn : fourier c θ ≠ 1) :
    ‖linearIntervalSum c m N θ‖ ≤ min (N : ℝ) (2/‖fourier c θ-1‖) := by
  apply le_min (actual_linear_interval_length_bound c m N θ)
  have hu : ‖fourier c θ‖ = 1 := Circle.norm_coe _
  have hm : ‖fourier (c*m) θ‖ = 1 := Circle.norm_coe _
  have hd : 0 < ‖fourier c θ-1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hn)
  have he := congrArg norm (actual_finite_geometric_telescoping (fourier c θ) N)
  rw [norm_mul] at he
  have hb : ‖(fourier c θ)^N-1‖ ≤ (2 : ℝ) := by
    calc
      _ ≤ ‖(fourier c θ)^N‖+‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow,hu,one_pow,norm_one]; norm_num
  rw [actual_linear_interval_geometric,norm_mul,hm,one_mul]
  apply (le_div_iff₀ hd).2
  calc
    _ = ‖(fourier c θ)^N-1‖ := by rw [mul_comm,he]
    _ ≤ 2 := hb

/-- At resonance the exact value retains the initial phase; the length
bound remains valid. No reciprocal bound is asserted here. -/
theorem actual_linear_interval_resonance (c m : ℤ) (N : ℕ)
    (θ : AddCircle (1 : ℝ)) (hz : fourier c θ = 1) :
    linearIntervalSum c m N θ = fourier (c*m) θ*(N : ℂ) := by
  rw [actual_linear_interval_geometric,hz]
  simp

end ActualOriginalLinearIntervalCancellation318
