module
public import ActualOriginalMajorArcIntegral318
public section
noncomputable section
namespace ActualOriginalArcDiagonal318
open QuadricCRTAssembly318 ActualOriginalFiniteMajorArcError318
open ActualOriginalNonzeroModeSum318 Filter
open scoped Topology ContDiff
set_option maxHeartbeats 16000000

/-- Both cutoffs at stage n are n. The actual scale is chosen only after
the proved finite arithmetic mass and fixed Fourier constants are available. -/
@[expose] def stageScale (A : ℕ → ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ)+1)^3 * (1+A n)

lemma stage_scale_bounds (A : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) (n : ℕ) :
    0 < stageScale A n ∧ (n : ℝ)+1 ≤ stageScale A n ∧ A n ≤ stageScale A n ∧
      ((n : ℝ)+1)^3 ≤ stageScale A n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hc : (n : ℝ)+1 ≤ ((n : ℝ)+1)^3 := by nlinarith [sq_nonneg (n : ℝ), mul_nonneg hn (sq_nonneg (n : ℝ))]
  have hc1 : 1 ≤ ((n : ℝ)+1)^3 := by linarith
  have hm : ((n : ℝ)+1)^3 ≤ stageScale A n := by
    unfold stageScale
    nlinarith [mul_nonneg (show 0 ≤ ((n : ℝ)+1)^3 by positivity) (hA n)]
  have ha : A n ≤ stageScale A n := by
    unfold stageScale
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (hA n)]
  exact ⟨by linarith,hc.trans hm,ha,hm⟩

lemma stage_scale_tendsto (A : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) :
    Tendsto (stageScale A) atTop atTop := by
  apply tendsto_atTop_mono (fun n => (stage_scale_bounds A hA n).2.1)
  exact tendsto_atTop_mono (fun n : ℕ => show (n : ℝ) ≤ (n : ℝ)+1 by linarith)
    tendsto_natCast_atTop_atTop

lemma stage_normalized_majorant (A : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) (n : ℕ) :
    A n / (stageScale A n)^6 ≤ 1/((n : ℝ)+1) := by
  obtain ⟨hB,hBn,hAB,hcube⟩ := stage_scale_bounds A hA n
  have hB1 : 1 ≤ stageScale A n := by have := Nat.cast_nonneg (R:=ℝ) n; linarith
  have h4 : 1 ≤ (stageScale A n)^4 := one_le_pow₀ hB1
  have h5 : stageScale A n ≤ (stageScale A n)^5 := by
    calc
      _ = stageScale A n * 1 := (mul_one _).symm
      _ ≤ stageScale A n * (stageScale A n)^4 := mul_le_mul_of_nonneg_left h4 hB.le
      _ = _ := by ring
  calc
    A n / (stageScale A n)^6 ≤ (stageScale A n)^5/(stageScale A n)^6 :=
      div_le_div_of_nonneg_right (hAB.trans h5) (by positivity)
    _ = 1/stageScale A n := by field_simp [hB.ne']; ring
    _ ≤ 1/((n : ℝ)+1) := one_div_le_one_div_of_le (by positivity) hBn

lemma stage_inverse_tendsto : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => show (n : ℝ) ≤ (n : ℝ)+1 by linarith)
      tendsto_natCast_atTop_atTop
  simpa only [one_div] using tendsto_inv_atTop_zero.comp hn

/-- One common scale sequence makes the FULL original nonzero-mode arc
sum negligible after the actual B^3 normalization, while BOTH cutoffs grow.
The finite mass is retained explicitly, including every bad modulus. -/
theorem actual_growing_arc_error (κ : ℕ) (hκ : 0 < κ)
    (W : Coordinates ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    ∃ B : ℕ → ℝ, (∀ n, 0 < B n) ∧ Tendsto B atTop atTop ∧
      (∀ n, ((n : ℝ)+1)^3 ≤ B n) ∧
      (∀ n, ‖finiteMajorArcError κ n (B n) (n : ℝ) W / (B n : ℂ)^3‖ ≤ 1/((n : ℝ)+1)) ∧
      Tendsto (fun n => finiteMajorArcError κ n (B n) (n : ℝ) W / (B n : ℂ)^3)
        atTop (𝓝 0) := by
  obtain ⟨k,C,hC,hbound⟩ := actual_finite_major_arc_error κ hκ W hW hWc
  let A : ℕ → ℝ := fun n => C*(1+(n : ℝ))^k*(2*(n : ℝ))*latticeSixthMass*finiteArcMass κ n
  have hA (n : ℕ) : 0 ≤ A n := by
    dsimp [A]
    have hm := finiteArcMass_nonneg κ n
    have hl := latticeSixthMass_nonneg
    positivity
  let B := stageScale A
  have hB (n : ℕ) : 0 < B n := (stage_scale_bounds A hA n).1
  have he (n : ℕ) :
      ‖finiteMajorArcError κ n (B n) (n : ℝ) W / (B n : ℂ)^3‖ ≤ 1/((n : ℝ)+1) := by
    have hh := hbound n (B n) (n : ℝ) (hB n) (Nat.cast_nonneg n)
    rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hB n)]
    calc
      _ ≤ (A n/(B n)^3)/(B n)^3 := div_le_div_of_nonneg_right hh (by positivity)
      _ = A n/(B n)^6 := by field_simp [(hB n).ne']; ring
      _ ≤ _ := stage_normalized_majorant A hA n
  exact ⟨B,hB,stage_scale_tendsto A hA,
    fun n => (stage_scale_bounds A hA n).2.2.2,he,squeeze_zero_norm he stage_inverse_tendsto⟩

end ActualOriginalArcDiagonal318
