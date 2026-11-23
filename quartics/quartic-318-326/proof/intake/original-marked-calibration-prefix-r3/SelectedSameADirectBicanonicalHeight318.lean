module
public import RationalSectionHeight318
public import InducedLattice318
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! The direct bicanonical consumer for the original selected surface.
The actual finite and archimedean pullbacks must refer to the same
nonzero vector Q=(dT)^2/P(T) of the relative dualizing square; dT
is not the differential of the value t in the number field. -/
public section
noncomputable section

namespace SelectedSameADirectBicanonicalHeight318

open NumberField SectionHeight318

variable {F : Type*} [Field F]

/-- Rational multiplier of the two integral bicanonical sections:
2765952000² / 1189580636160000 = 25725/4. -/
@[expose] def coefficientScale (F : Type*) [Field F] : F :=
  ((25725 / 4 : ℚ) : F)

/-- Coordinates of the two sections in the same rational bicanonical frame Q. -/
@[expose] def coefficients (t : ℚ) : Fin 2 → F :=
  ![coefficientScale F * (32 : F), coefficientScale F * (t : F)]

variable [NumberField F]

private theorem first_ne (t : ℚ) : (coefficients (F := F) t) 0 ≠ 0 := by
  change coefficientScale F * (32 : F) ≠ 0
  unfold coefficientScale
  norm_num

private theorem coefficient_ratio (t : ℚ) :
    (coefficients (F := F) t) 1 = ((t / 32 : ℚ) : F) * coefficients t 0 := by
  change coefficientScale F * (t : F) =
    ((t / 32 : ℚ) : F) * (coefficientScale F * (32 : F))
  push_cast
  ring

omit [NumberField F] in
private theorem scale_norm (v : InfinitePlace F) :
    v (coefficientScale F) = 25725 / 4 := by
  rw [coefficientScale, v.map_ratCast, ← Rat.norm_cast_real, Real.norm_eq_abs]
  norm_num

omit [NumberField F] in
private theorem coefficient_norm_bound (v : InfinitePlace F) (t : ℚ) (i : Fin 2) :
    v (coefficients t i) ≤ (25725 / 4 : ℝ) * max 32 (v (t : F)) := by
  have hs : (0 : ℝ) ≤ 25725 / 4 := by norm_num
  fin_cases i
  · change v.val (coefficientScale F * (32 : F)) ≤ _
    rw [map_mul]
    change v (coefficientScale F) * v ((32 : ℕ) : F) ≤ _
    rw [scale_norm, v.map_natCast]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hs
  · change v.val (coefficientScale F * (t : F)) ≤ _
    rw [map_mul]
    change v (coefficientScale F) * v (t : F) ≤ _
    rw [scale_norm]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hs

/-- The actual Petersson read of Q and weighted compact comparison imply
the uniform archimedean bound on both literal coefficients at this place. -/
theorem arch_section_bound (t : ℚ) (Q : FrameNorms F)
    (v : InfinitePlace F) (U f : ℝ)
    (hU : 2 * max 32 (v (t : F)) ≤ U) (hf : 64 ≤ f)
    (hQ : Q.arch v = 4 / (U * f)) (i : Fin 2) :
    v (coefficients t i) * Q.arch v ≤ 25725 / 128 := by
  have hUpos : 0 < U := by linarith only [hU, le_max_left (32 : ℝ) (v (t : F))]
  have hfpos : 0 < f := by linarith only [hf]
  rw [hQ, ← mul_div_assoc]
  apply (div_le_iff₀ (mul_pos hUpos hfpos)).2
  calc
    v (coefficients t i) * 4 ≤ ((25725 / 4 : ℝ) * max 32 (v (t : F))) * 4 :=
      mul_le_mul_of_nonneg_right (coefficient_norm_bound v t i) (by norm_num)
    _ = (25725 / 128 : ℝ) * ((2 * max 32 (v (t : F))) * 64) := by ring
    _ ≤ (25725 / 128 : ℝ) * (U * f) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hU hf (by norm_num) hUpos.le) (by norm_num)

/-- The integral image 210·D² and the sharp infinity bound consume less than 11. -/
theorem strict_log_allowance : Real.log 210 + Real.log (25725 / 128) < 11 := by
  rw [← Real.log_mul (by norm_num : (210 : ℝ) ≠ 0) (by norm_num : (25725 / 128 : ℝ) ≠ 0)]
  rw [show (210 : ℝ) * (25725 / 128) = 2701125 / 64 by norm_num]
  have h := Real.log_lt_log (by norm_num : 0 < ((2701125 : ℝ) / 64)^4)
    (by norm_num : ((2701125 : ℝ) / 64)^4 < (2 : ℝ)^62)
  rw [Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

/-- The literal section-height inequality. No normalized inverse KS, rational
Hodge coefficient or period matrix appears. Here hY is the degree of the
actual unsquared Hodge line (Yuan normalization), and Q carries its own
actual bicanonical lattice and Petersson metric. -/
theorem height_of_local_data (t : ℚ) (Q : FrameNorms F) (hY : ℝ)
    (degree : Q.normalizedDegree = 2 * hY + Real.log 210)
    (harch : ∀ v : InfinitePlace F, ∃ U f : ℝ,
      2 * max 32 (v (t : F)) ≤ U ∧ 64 ≤ f ∧ Q.arch v = 4 / (U * f))
    (hfinite : ∀ (v : FinitePlace F) i, v (coefficients t i) * Q.finiteNorm v ≤ 1) :
    Height.logHeight₁ (t / 32) < 2 * hY + 11 := by
  have ha (v : InfinitePlace F) (i : Fin 2) :
      v (coefficients t i) * Q.arch v ≤ 25725 / 128 := by
    obtain ⟨U, f, hU, hf, hQ⟩ := harch v
    exact arch_section_bound t Q v U f hU hf hQ i
  have he : (![coefficients (F := F) t 0, coefficients t 1] : Fin 2 → F) =
      coefficients t := by
    funext i
    fin_cases i <;> rfl
  have h := rational_section_height
    (coefficients (F := F) t 0) (coefficients (F := F) t 1) (t / 32)
    (first_ne t) (coefficient_ratio t) Q (25725 / 128) (by
      rw [he]
      exact ha) (by
      rw [he]
      exact hfinite)
  rw [degree] at h
  linarith only [h, strict_log_allowance]

/-- Compose the same raw KS image/isometry in frame ξ=Ψ(η²) with the
actual frame change Q=c·ξ. Over an actual selected marked model the KS
norm equation comes from Yuan's image and raw archimedean isometry, not
from an arbitrary algebraic isomorphism. -/
theorem height_of_raw_ks (t : ℚ) (Q Xi H : FrameNorms F)
    (c : F) (hc : c ≠ 0) (frame : Q = Xi.rescale c hc)
    (hKS : InducedLattice318.induced Xi (210 : F) (by norm_num) = InducedLattice318.square H)
    (harch : ∀ v : InfinitePlace F, ∃ U f : ℝ,
      2 * max 32 (v (t : F)) ≤ U ∧ 64 ≤ f ∧ Q.arch v = 4 / (U * f))
    (hfinite : ∀ (v : FinitePlace F) i, v (coefficients t i) * Q.finiteNorm v ≤ 1) :
    Height.logHeight₁ (t / 32) < 2 * H.normalizedDegree + 11 := by
  have hD : Q.normalizedDegree = 2 * H.normalizedDegree + Real.log 210 := calc
    Q.normalizedDegree = (Xi.rescale c hc).normalizedDegree :=
      congrArg FrameNorms.normalizedDegree frame
    _ = Xi.normalizedDegree := Xi.normalizedDegree_rescale c hc
    _ = 2 * H.normalizedDegree + Real.log 210 := InducedLattice318.ks_degree Xi H hKS
  exact height_of_local_data t Q H.normalizedDegree hD harch hfinite

end SelectedSameADirectBicanonicalHeight318

#print axioms SelectedSameADirectBicanonicalHeight318.height_of_raw_ks
