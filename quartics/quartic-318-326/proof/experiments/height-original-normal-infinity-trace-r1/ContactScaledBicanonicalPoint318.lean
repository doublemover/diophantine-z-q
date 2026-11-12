module
public import ContactBicanonicalPointValue318
public section
noncomputable section
namespace ContactScaledBicanonicalPoint318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c : Fin 4 → ℚˣ) (t : ℚ)
    (hn : ∀ i, RationalContactPoint318.parameters c t i ≠ 0)

/-- Literal integer used in the original metric comparison. Scaling here
is of actual global tensor sections, and does not assert integral extension. -/
@[expose] def J : ℕ := 2765952000
@[expose] def scaledQ0 : Γ(ContactGlobalBicanonical318.tensor c, ⊤) :=
  J^2 • ContactGlobalBicanonical318.q0 c
@[expose] def scaledQ1 : Γ(ContactGlobalBicanonical318.tensor c, ⊤) :=
  J^2 • ContactGlobalBicanonical318.q1 c

/-- Restriction, intrinsic frame, global affine section comparison and the
original point all preserve integer scaling of genuine sections. -/
theorem value_nsmul (i : Fin 4) (n : ℕ)
    (q : Γ(ContactGlobalBicanonical318.tensor c, ⊤)) :
    ContactBicanonicalPointValue318.value c t hn i (n • q) =
      n • ContactBicanonicalPointValue318.value c t hn i q := by
  unfold ContactBicanonicalPointValue318.value
  simp only [map_nsmul, IntrinsicTensorFrameValue318.sectionValue_nsmul]

theorem scaledQ0_ne (i : Fin 4) :
    ContactBicanonicalPointValue318.value c t hn i (scaledQ0 c) ≠ 0 := by
  rw [scaledQ0, value_nsmul, nsmul_eq_mul]
  exact mul_ne_zero (by norm_num [J]) (ContactBicanonicalPointValue318.value_q0_ne c t hn i)

theorem scaled_ratio (i : Fin 4) :
    ContactBicanonicalPointValue318.value c t hn i (scaledQ1 c) =
      algebraMap ℚ (RationalContactPoint318.PointField c t) t *
        ContactBicanonicalPointValue318.value c t hn i (scaledQ0 c) := by
  rw [scaledQ1, scaledQ0, value_nsmul, value_nsmul,
    ContactBicanonicalPointValue318.value_ratio, nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- The actual J²-scaled global bicanonical pair supplies the exact
nonzero first value and ratio required by the scalar part of MetricSections. -/
theorem original_scaled_sections (u v : ℤ)
    (hf : ∀ j : Fin 5, ContactRadical318.forms u v j ≠ 0) (i : Fin 4) :
    let t := 32 * ((u : ℚ) / (v : ℚ))
    let hn := RationalContactPoint318.parameters_ne_of_forms c u v hf
    ContactBicanonicalPointValue318.value c t hn i (scaledQ0 c) ≠ 0 ∧
      ContactBicanonicalPointValue318.value c t hn i (scaledQ1 c) =
        algebraMap ℚ (RationalContactPoint318.PointField c t) t *
          ContactBicanonicalPointValue318.value c t hn i (scaledQ0 c) :=
  ⟨scaledQ0_ne c _ _ i, scaled_ratio c _ _ i⟩
end ContactScaledBicanonicalPoint318
