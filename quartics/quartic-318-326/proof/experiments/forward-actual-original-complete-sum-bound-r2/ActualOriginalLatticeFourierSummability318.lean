module
public import ActualOriginalIntegerLattice318
public section
noncomputable section
namespace ActualOriginalLatticeFourierSummability318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318
open ActualOriginalUniformTranslateSupport318 ActualOriginalIntegerLattice318
open ActualOriginalCoordinateFrequency318
open scoped ContDiff
set_option maxHeartbeats 16000000

/-- Full-coordinate decay now yields absolute summability over the
actual dual integer lattice. The exceptional zero frequency is handled by
a finite-exception argument, not bounded by an inverse power vanishing at0.
The fixed-beta dependence of the decay constant is retained. -/
theorem actual_original_lattice_fourier_summable (κ β : ℝ) (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    Summable (fun z : Coordinates ℤ => ‖originalCoordinateFourier κ β W (integerEmbed z)‖) ∧
      Summable (fun z : Coordinates ℤ => originalCoordinateFourier κ β W (integerEmbed z)) := by
  obtain ⟨C,hC⟩ := actual_original_coordinate_decay κ β W hW hWc 6
  have hs : Summable (fun z : Coordinates ℤ => ‖originalCoordinateFourier κ β W (integerEmbed z)‖) := by
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
      ‖originalCoordinateFourier κ β W (integerEmbed z)‖ ≤ C / ‖integerEmbed z‖^6 :=
        (le_div_iff₀ (pow_pos hn 6)).mpr (by simpa only [mul_comm] using hC (integerEmbed z))
      _ = C * (‖integerEmbed z‖⁻¹)^6 := by rw [div_eq_mul_inv,inv_pow]
  exact ⟨hs,hs.of_norm⟩

end ActualOriginalLatticeFourierSummability318
