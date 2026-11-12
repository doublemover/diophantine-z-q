module
public import ActualOriginalTorusPeriodization318
public section
noncomputable section
namespace ActualOriginalCompactFourier318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalUniformTranslateSupport318 ActualOriginalIntegerLattice318
open ActualOriginalCoordinateFrequency318 ActualFullDualFourierDecay318 MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 16000000

/-- The compact source meets only finitely many original integer
points, so the primal lattice sum is absolutely convergent as well. -/
lemma actual_compact_lattice_norm_summable (f : Coordinates ℝ → ℂ)
    (hc : HasCompactSupport f) :
    Summable (fun z : Coordinates ℤ => ‖f (integerEmbed z)‖) := by
  classical
  obtain ⟨s,hs⟩ := actual_uniform_translate_support f hc
    (isCompact_singleton (x:=(0 : Coordinates ℝ)))
  apply summable_of_hasFiniteSupport
  apply s.finite_toSet.subset
  intro z hz
  by_contra hnot
  apply hz
  apply norm_eq_zero.mpr
  simpa only [add_zero] using hs 0 (by simp) z hnot

/-- Fourier transform in the same original product volume and full
coordinate pairing, now for an arbitrary complex smooth compact input. -/
@[expose] def compactFourier (f : Coordinates ℝ → ℂ) (y : Coordinates ℝ) : ℂ :=
  ∫ x : Coordinates ℝ, Real.fourierChar (-frequency y x) • f x

lemma actual_compact_fourier_decay (f : Coordinates ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (n : ℕ) :
    ∃ C : ℝ, ∀ y : Coordinates ℝ, ‖y‖^n * ‖compactFourier f y‖ ≤ C := by
  obtain ⟨C,hC⟩ := actual_full_dual_power_bound (hc.toSchwartzMap hf) n
  refine ⟨C,fun y => ?_⟩
  have h := hC (frequency y)
  change ‖frequency y‖^n * ‖compactFourier f y‖ ≤ C at h
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (actual_coordinate_norm_le_dual y) n)
    (norm_nonneg _)).trans h

/-- Produced absolute dual-lattice summability for arbitrary original
smooth compact complex input. Zero is retained as the unique finite exception
to the inverse-sixth-power comparison. -/
theorem actual_compact_fourier_lattice_summable (f : Coordinates ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Summable (fun z : Coordinates ℤ => ‖compactFourier f (integerEmbed z)‖) ∧
      Summable (fun z : Coordinates ℤ => compactFourier f (integerEmbed z)) := by
  obtain ⟨C,hC⟩ := actual_compact_fourier_decay f hf hc 6
  have hs : Summable (fun z : Coordinates ℤ => ‖compactFourier f (integerEmbed z)‖) := by
    apply Summable.of_norm_bounded_eventually (actual_integer_norm_inverse_six.mul_left C)
    apply Filter.mem_cofinite.mpr
    apply (Set.finite_singleton (0 : Coordinates ℤ)).subset
    intro z hz
    by_contra hz0
    have hzne : z ≠ 0 := by simpa only [Set.mem_singleton_iff] using hz0
    have hem : integerEmbed z ≠ 0 := by
      intro he
      apply hzne
      apply actual_integer_embedding_closed.injective
      simpa only [integerEmbed_zero] using he
    have hn : 0 < ‖integerEmbed z‖ := norm_pos_iff.mpr hem
    apply hz
    simp only [norm_norm]
    calc
      ‖compactFourier f (integerEmbed z)‖ ≤ C / ‖integerEmbed z‖^6 :=
        (le_div_iff₀ (pow_pos hn 6)).mpr (by simpa only [mul_comm] using hC (integerEmbed z))
      _ = C * (‖integerEmbed z‖⁻¹)^6 := by rw [div_eq_mul_inv,inv_pow]
  exact ⟨hs,hs.of_norm⟩

end ActualOriginalCompactFourier318
