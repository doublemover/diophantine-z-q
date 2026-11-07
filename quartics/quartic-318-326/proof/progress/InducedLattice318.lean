module
public import SectionHeight318
public section
noncomputable section
namespace InducedLattice318
open NumberField Height SectionHeight318
set_option maxHeartbeats 0
variable {K : Type*} [Field K] [NumberField K]

/-- Replace the integral lattice M by c M and retain the induced infinite
metrics, using the same nonzero generic frame. This is not frame rescaling. -/
@[expose] def induced (F : FrameNorms K) (c : K) (hc : c ≠ 0) : FrameNorms K where
  arch := F.arch
  finiteNorm v := F.finiteNorm v / v.val c
  arch_pos := F.arch_pos
  finite_pos v := div_pos (F.finite_pos v) (v.val.pos hc)
  finite_support := F.finite_support.div (FinitePlace.hasFiniteMulSupport hc)

/-- The induced sublattice has its exact finite-place degree correction. -/
theorem induced_degree (F : FrameNorms K) (c : K) (hc : c ≠ 0) :
    (induced F c hc).normalizedDegree = F.normalizedDegree -
      (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (v.val c)) /
        (Module.finrank ℚ K : ℝ) := by
  have hF := log_finite_support F.finite_support
  have hcfin := log_finite_support (FinitePlace.hasFiniteMulSupport hc)
  have hcn : ∀ v : FinitePlace K, v.val c ≠ 0 := fun v => v.val.ne_zero_iff.mpr hc
  have hfinite : (∑ᶠ v : FinitePlace K, Real.log (F.finiteNorm v / v.val c)) =
      (∑ᶠ v : FinitePlace K, Real.log (F.finiteNorm v)) -
      (∑ᶠ v : FinitePlace K, Real.log (v.val c)) := by
    simp_rw [Real.log_div (F.finite_pos _).ne' (hcn _)]
    exact finsum_sub_distrib hF hcfin
  have hprod := scalar_log_sum_zero c hc
  unfold FrameNorms.normalizedDegree FrameNorms.logSum induced
  dsimp only
  rw [hfinite]
  have he : (∑ᶠ v : FinitePlace K, Real.log (v.val c)) =
      -(∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (v.val c)) := by linarith
  rw [he]
  ring

/-- Multiplication of the lattice by a positive rational integer subtracts
log n from normalized degree, independently of the number field degree. -/
theorem induced_nat_degree (F : FrameNorms K) (n : ℕ) (hn : 0 < n) :
    (induced F (n : K) (by exact_mod_cast hn.ne')).normalizedDegree =
      F.normalizedDegree - Real.log n := by
  rw [induced_degree]
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hs : (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (v.val (n : K))) =
      (Module.finrank ℚ K : ℝ) * Real.log n := by
    simp_rw [show ∀ v : InfinitePlace K, v.val (n : K) = (n : ℝ) from
      fun v => v.map_natCast n]
    rw [← Finset.sum_mul, ← Nat.cast_sum, InfinitePlace.sum_mult_eq]
  rw [hs, mul_div_cancel_left₀ _ hd]

/-- Tensor square of an actual metrized-line frame at every place. -/
@[expose] def square (F : FrameNorms K) : FrameNorms K where
  arch v := F.arch v ^ 2
  finiteNorm v := F.finiteNorm v ^ 2
  arch_pos v := pow_pos (F.arch_pos v) _
  finite_pos v := pow_pos (F.finite_pos v) _
  finite_support := F.finite_support.pow 2

theorem square_degree (F : FrameNorms K) :
    (square F).normalizedDegree = 2 * F.normalizedDegree := by
  unfold FrameNorms.normalizedDegree FrameNorms.logSum square
  dsimp only
  simp_rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have ha : (∑ v : InfinitePlace K, (v.mult : ℝ) * (2 * Real.log (F.arch v))) =
      2 * ∑ v : InfinitePlace K, (v.mult : ℝ) * Real.log (F.arch v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [ha, ← mul_finsum]
  ring

/-- The exact numerical KS conclusion follows from equality of the actual
image-lattice frame norms with the squared Hodge frame norms. -/
theorem ks_degree (F H : FrameNorms K)
    (hKS : induced F (210 : K) (by norm_num) = square H) :
    F.normalizedDegree = 2 * H.normalizedDegree + Real.log 210 := by
  have h := congrArg FrameNorms.normalizedDegree hKS
  have hi := induced_nat_degree F 210 (by norm_num)
  norm_num only [Nat.cast_ofNat] at hi
  rw [hi, square_degree] at h
  linarith

end InducedLattice318
