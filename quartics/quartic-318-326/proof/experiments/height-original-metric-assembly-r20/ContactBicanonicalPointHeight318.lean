module
public import ContactScaledBicanonicalPoint318
public import RationalSectionHeight318
public section
noncomputable section
namespace ContactBicanonicalPointHeight318
open AlgebraicGeometry NumberField
set_option maxHeartbeats 400000
attribute [-instance] DivisionRing.toRatAlgebra
/-- Degree for the field's canonical rational module. Defining this with an
abstract field prevents a quotient-presentation module instance from silently
replacing the one used by the number-field height theorem. -/
@[expose] def fieldDegree (K : Type*) [Field K] [NumberField K] : ℕ :=
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  Module.finrank ℚ K

variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i, RationalContactPoint318.parameters c t i ≠ 0)

/-- Values of the actual J²-scaled global pair in an original branch frame. -/
@[expose] def a0 (i : Fin 4) : RationalContactPoint318.PointField c t :=
  ContactBicanonicalPointValue318.value c t hn i
    (ContactScaledBicanonicalPoint318.scaledQ0 c)
@[expose] def a1 (i : Fin 4) : RationalContactPoint318.PointField c t :=
  ContactBicanonicalPointValue318.value c t hn i
    (ContactScaledBicanonicalPoint318.scaledQ1 c)

theorem a0_ne (i : Fin 4) : a0 c t hn i ≠ 0 :=
  ContactScaledBicanonicalPoint318.scaledQ0_ne c t hn i

theorem ratio (i : Fin 4) : a1 c t hn i =
    (t : RationalContactPoint318.PointField c t) * a0 c t hn i := by
  have hc : algebraMap ℚ (RationalContactPoint318.PointField c t) t =
      (t : RationalContactPoint318.PointField c t) := map_ratCast _ t
  simpa only [a0, a1, hc] using ContactScaledBicanonicalPoint318.scaled_ratio c t hn i

/-- The height of the actual pair is normalized by the degree of its actual
point field. Specialization need not have degree sixteen. -/
theorem normalized_height (i : Fin 4) :
    Height.logHeight ![a0 c t hn i, a1 c t hn i] /
      (fieldDegree (RationalContactPoint318.PointField c t) : ℝ) =
        Height.logHeight₁ t :=
  SectionHeight318.rational_ratio_height _ _ t (a0_ne c t hn i) (ratio c t hn i)

/-- Exact change between two of the four evaluated frames. This is a
nonzero field scalar, not an identification of their local norms. -/
@[expose] def frameScalar (i j : Fin 4) : RationalContactPoint318.PointField c t :=
  a0 c t hn j / a0 c t hn i

theorem frameScalar_ne (i j : Fin 4) : frameScalar c t hn i j ≠ 0 :=
  div_ne_zero (a0_ne c t hn j) (a0_ne c t hn i)

theorem frameScalar_a0 (i j : Fin 4) :
    a0 c t hn j = frameScalar c t hn i j * a0 c t hn i := by
  unfold frameScalar
  rw [div_mul_cancel₀ _ (a0_ne c t hn i)]

theorem frameScalar_a1 (i j : Fin 4) :
    a1 c t hn j = frameScalar c t hn i j * a1 c t hn i := by
  rw [ratio c t hn j, ratio c t hn i, frameScalar_a0 c t hn i j]
  ring

/-- All four original branch evaluations give the same absolute height. -/
theorem normalized_height_frame_independent (i j : Fin 4) :
    Height.logHeight ![a0 c t hn i, a1 c t hn i] /
      (fieldDegree (RationalContactPoint318.PointField c t) : ℝ) =
    Height.logHeight ![a0 c t hn j, a1 c t hn j] /
      (fieldDegree (RationalContactPoint318.PointField c t) : ℝ) := by
  rw [normalized_height, normalized_height]

/-- The exact original coordinate is recovered by dividing the second
actual section value by 32 times the first, retaining the factor 32. -/
theorem original_coordinate (u v : ℤ)
    (hf : ∀ j : Fin 5, ContactRadical318.forms u v j ≠ 0) (i : Fin 4) :
    let t := 32 * ((u : ℚ) / (v : ℚ))
    let hn := RationalContactPoint318.parameters_ne_of_forms c u v hf
    a1 c t hn i / (32 * a0 c t hn i) =
      (((u : ℚ) / (v : ℚ) : ℚ) : RationalContactPoint318.PointField c t) := by
  dsimp only
  apply (div_eq_iff (mul_ne_zero (by norm_num) (a0_ne c _ _ i))).2
  rw [ratio]
  push_cast
  ring

end ContactBicanonicalPointHeight318
