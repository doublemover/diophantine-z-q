module
public import ActualOriginalUniformPairedMixedConstants318
public section
noncomputable section
namespace ActualOriginalScaledPairedMixedDifference318
open QuadricCRTAssembly318 ActualOriginalIntegerTiling318 ActualOriginalCompactCircleCount318
open ActualOriginalUniformPairedMixedConstants318 ActualOriginalTwoAxisSliceIdentity318
open scoped ContDiff

@[expose] def latticePairedWeight (B : ℝ) (W : Coordinates ℝ → ℝ)
    (h z : Coordinates ℤ) : ℂ := latticeWeight B W (h+z)*starRingEnd ℂ (latticeWeight B W z)

lemma actual_lattice_pair_real (B : ℝ) (W : Coordinates ℝ → ℝ) (h z : Coordinates ℤ) :
    latticePairedWeight B W h z=
      (translatedPairedWeight W (B⁻¹ • integerEmbed h) (B⁻¹ • integerEmbed z) : ℂ) := by
  simp [latticePairedWeight,latticeWeight,translatedPairedWeight,integerEmbed_add,smul_add,add_comm]

lemma actual_plane_pair_value (B : ℝ) (W : Coordinates ℝ → ℝ) (h : Coordinates ℤ)
    (lo₀ lo₁ c d e : ℤ) (i j : ℕ) :
    planePairedWeight (latticeWeight B W) h lo₀ lo₁ c d e i j=
      latticePairedWeight B W h (planePoint lo₀ lo₁ c d e i j) := rfl

/-- ACTUAL scaled paired-weight mixed increments are now PRODUCED at
order1/B², uniformly in every lattice displacement,base point and direction.
The constants depend only on the original smooth compact W. -/
theorem actual_scaled_paired_mixed_constants (W : Coordinates ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) :
    ∃ A L D : ℝ, 0≤A ∧ 0≤L ∧ 0≤D ∧ ∀ B : ℝ, 0<B → ∀ h z : Coordinates ℤ,
      ‖latticePairedWeight B W h z‖≤A^2 ∧
      (∀ u, ‖latticePairedWeight B W h z-latticePairedWeight B W h (z+u)‖≤
        (2*A*L/B)*‖integerEmbed u‖) ∧
      (∀ u v, ‖(latticePairedWeight B W h z-latticePairedWeight B W h (z+u))-
        (latticePairedWeight B W h (z+v)-latticePairedWeight B W h (z+v+u))‖≤
          ((2*A*D+2*L^2)/B^2)*‖integerEmbed u‖*‖integerEmbed v‖) := by
  obtain ⟨A,L,D,hA,hL,hD,hall⟩ := actual_smooth_uniform_paired_mixed_constants W hW hc
  refine ⟨A,L,D,hA,hL,hD,fun B hB h z => ?_⟩
  have hh := hall (B⁻¹ • integerEmbed h) (B⁻¹ • integerEmbed z)
  refine ⟨?_,?_,?_⟩
  · simpa only [actual_lattice_pair_real,Complex.norm_real] using hh.1
  · intro u
    have hu := hh.2.1 (B⁻¹ • integerEmbed u)
    simp only [actual_lattice_pair_real,←Complex.ofReal_sub,Complex.norm_real,integerEmbed_add,smul_add]
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hB] at hu
    convert hu using 1 <;> ring
  · intro u v
    have huv := hh.2.2 (B⁻¹ • integerEmbed u) (B⁻¹ • integerEmbed v)
    simp only [actual_lattice_pair_real,←Complex.ofReal_sub,Complex.norm_real,integerEmbed_add,smul_add]
    simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hB] at huv
    convert huv using 1 <;> simp only [div_eq_mul_inv,inv_pow] <;> ring

end ActualOriginalScaledPairedMixedDifference318
