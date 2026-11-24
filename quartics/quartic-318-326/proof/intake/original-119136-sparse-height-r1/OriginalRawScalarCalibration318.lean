module
public import OriginalMarkedHeightCalibration318
public section
noncomputable section

namespace OriginalRawScalarCalibration318

open NumberField OriginalMarkedHeightCalibration318

/-- The ordinary exact quartic. Use the marked T (32u/v), not the height
coordinate T/32. This factor order is the homogeneous finite receiver's. -/
@[expose] def P {F : Type*} [CommRing F] (t : F) : F :=
  t * (t - 32) * (t - 76832) * (t + 343)

theorem map_P {F K : Type*} [CommRing F] [CommRing K] (σ : F →+* K) (t : F) :
    σ (P t) = P (σ t) := by
  simp only [P, map_mul, map_sub, map_add, map_ofNat]

theorem denominator_eq_norm (z : ℂ) : denominator z = ‖P z‖ := by
  simp only [P, denominator, norm_mul, sub_neg_eq_add]
  ring

/-- The one algebraic noncontact certificate supplies complex positivity at
EVERY embedding. It is not a new per-place analytic assumption. -/
theorem denominator_pos {F : Type*} [Field F] (σ : F →+* ℂ) (t : F)
    (ht : P t ≠ 0) : 0 < denominator (σ t) := by
  rw [denominator_eq_norm, ← map_P]
  exact norm_pos_iff.mpr (fun h => ht (σ.injective (h.trans (map_zero σ).symm)))

/-- The actual rational coefficient Q/Ψ(η²); the frame B is read once in the
original raw determinant, not chosen anew at each infinite place. -/
@[expose] def coefficient {F : Type*} [Field F] (t B : F) : F := (P t * B)⁻¹

/-- Squared ordinary derivative and all units kept in the complex signed
identity until the coefficient is read. Cancels exactly the raw 210, not a
separately normalized Ψ/210. This does not infer the signed identity from
norm equality. -/
theorem complex_raw_norm (z B a k : ℂ) (hz : 0 < denominator z)
    (ha : a ≠ 0) (hk : k ≠ 0)
    (raw : B = 210 * k^2 / (((2 * (Real.pi : ℂ)) * Complex.I)^2 * a^2)) :
    ‖coefficient z B‖ =
      ‖a‖^2 / denominator z * (2 * Real.pi)^2 / (210 * ‖k‖^2) := by
  have hθ : ‖(2 * (Real.pi : ℂ)) * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    norm_num [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [coefficient, norm_inv, norm_mul, ← denominator_eq_norm, raw,
    norm_div, norm_mul, norm_pow, norm_mul, norm_pow, norm_pow, hθ]
  norm_num only [show ‖(210 : ℂ)‖ = 210 by norm_num]
  have hp : 0 < 2 * Real.pi := by positivity
  field_simp [hz.ne', (norm_ne_zero_iff.mpr ha), (norm_ne_zero_iff.mpr hk), hp.ne']

/-- Take the original complex germ (τ,a,k), not fictitious real radii.
The compact inequality and the actual metric on the classified Hodge wedge
remain genuine geometric inputs on this same germ. -/
def from_signed_period {E : Type*} [Field E] [NumberField E]
    (w : InfinitePlace E) (t : ℚ) (B : E) (τ a k : ℂ) (A : ℝ)
    (hτ : 0 < τ.im) (ha : a ≠ 0) (hk : k ≠ 0)
    (ht : P (t : E) ≠ 0)
    (raw : w.embedding B =
      210 * k^2 / (((2 * (Real.pi : ℂ)) * Complex.I)^2 * a^2))
    (squareMetric : A^2 = 210 * ‖k‖^2 * τ.im^2 / Real.pi^2)
    (compact : 64 * (SelectedActualSameACurvature64.metricU (w.embedding (t : E)) *
      ‖a‖^2 * τ.im^2) ≤ denominator (w.embedding (t : E))) :
    AtPlace (w.embedding (t : E)) (w.val (coefficient (t : E) B)) A where
  derivativeNorm := ‖a‖
  imaginary := τ.im
  periodNorm := ‖k‖
  derivative_pos := norm_pos_iff.mpr ha
  imaginary_pos := hτ
  period_pos := norm_pos_iff.mpr hk
  noncontact := denominator_pos w.embedding _ ht
  compact_read := compact
  hodge_sq := squareMetric
  raw_norm := by
    have hh := complex_raw_norm (w.embedding (t : E)) (w.embedding B) a k
      (denominator_pos w.embedding _ ht) ha hk raw
    have hb : w.embedding (coefficient (t : E) B) =
        coefficient (w.embedding (t : E)) (w.embedding B) := by
      simp only [coefficient, map_inv₀, map_mul, map_P]
    calc
      w.val (coefficient (t : E) B) = ‖w.embedding (coefficient (t : E) B)‖ :=
        (InfinitePlace.norm_embedding_eq w (coefficient (t : E) B)).symm
      _ = _ := by rw [hb]; exact hh

/-- Exact arch binder of the finite trait/overlap route. The statement uses
the same raw coefficient, finite-field embedding and hodgeNorm as R8. -/
theorem finite_period {E : Type*} [Field E] [NumberField E]
    (w : InfinitePlace E) (t : ℚ) (B : E) (A : ℝ)
    (R : AtPlace (w.embedding (t : E)) (w.val (coefficient (t : E) B)) A) :
    ∃ U h : ℝ, 2 * max 32 (w (t : E)) ≤ U ∧ 64 ≤ h ∧
      w.val ((P (t : E) * B)⁻¹) * A^2 = 4 / (U * h) := by
  have hp := at_place_bound R
  rw [InfinitePlace.norm_embedding_eq] at hp
  exact hp

end OriginalRawScalarCalibration318

#print axioms OriginalRawScalarCalibration318.complex_raw_norm
#print axioms OriginalRawScalarCalibration318.from_signed_period
#print axioms OriginalRawScalarCalibration318.finite_period
