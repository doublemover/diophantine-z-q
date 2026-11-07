module
public import HorizontalIntegralCharts318
public section
noncomputable section
namespace SourceHorizontalSections318
open VerticalSection318 AlgebraicSectionPullback318 HorizontalIntegralCharts318 IsLocalRing
set_option maxHeartbeats 0
variable {R B K : Type*} [CommRing R] [CommRing B] [IsLocalRing B] [Algebra ℚ B]
  [Field K] [Algebra B K] [Algebra R K]

theorem scaled0_identity (D : Derivation R K K) (t : K) :
    section0 D t = (J : K)^2 * coefficient0 D t := by
  unfold section0 coefficient0
  ring

theorem scaled1_identity (D : Derivation R K K) (t : K) :
    section1 D t = (J : K)^2 * coefficient1 D t := by
  unfold section1 section0 coefficient1 coefficient0
  ring

/-- The published scale J is a unit horizontally, so scaling preserves the
proved lack of a common zero, not just integrality. -/
theorem scale_integral_pair (D : Derivation R K K) (t : K)
    (h : ∃ b0 b1 : B, (IsUnit b0 ∨ IsUnit b1) ∧
      algebraMap B K b0 = coefficient0 D t ∧ algebraMap B K b1 = coefficient1 D t) :
    ∃ c0 c1 : B, (IsUnit c0 ∨ IsUnit c1) ∧
      algebraMap B K c0 = section0 D t ∧ algebraMap B K c1 = section1 D t := by
  obtain ⟨b0,b1,hu,h0,h1⟩ := h
  have hJ : IsUnit ((J : B)^2) := (integer_isUnit J (by norm_num [J])).pow 2
  refine ⟨(J : B)^2*b0, (J : B)^2*b1, hu.imp (hJ.mul ·) (hJ.mul ·), ?_, ?_⟩
  · rw [map_mul, map_pow, map_intCast, h0, scaled0_identity]
  · rw [map_mul, map_pow, map_intCast, h1, scaled1_identity]

variable [IsDomain B] [IsFractionRing B K]

theorem finite_branch_scaled_sections (D : Derivation R K K) (i : Fin 4) (z : B)
    (hz : z ∈ maximalIdeal B) (hz0 : z ≠ 0) (hDz : D (algebraMap B K z) = 1) :
    ∃ c0 c1 : B, (IsUnit c0 ∨ IsUnit c1) ∧
      algebraMap B K c0 = section0 D ((contacts i : K) + (algebraMap B K z)^2) ∧
      algebraMap B K c1 = section1 D ((contacts i : K) + (algebraMap B K z)^2) := by
  obtain ⟨b0,b1,hu,h0,h1⟩ := finite_derivation_integrality D i z hz hz0 hDz
  exact scale_integral_pair D _ ⟨b0,b1,Or.inl hu,h0,h1⟩

theorem infinity_scaled_sections (D : Derivation R K K) (z : B)
    (hz : z ∈ maximalIdeal B) (hz0 : z ≠ 0) (hDz : D (algebraMap B K z) = 1) :
    ∃ c0 c1 : B, (IsUnit c0 ∨ IsUnit c1) ∧
      algebraMap B K c0 = section0 D (1 / (algebraMap B K z)^2) ∧
      algebraMap B K c1 = section1 D (1 / (algebraMap B K z)^2) := by
  obtain ⟨b0,b1,hu,h0,h1⟩ := infinity_derivation_integrality D z hz hz0 hDz
  exact scale_integral_pair D _ ⟨b0,b1,Or.inr hu,h0,h1⟩

theorem regular_scaled_sections (D : Derivation R K K) (t : B)
    (ht : ∀ i : Fin 4, residue B t ≠ residue B (contacts i : B))
    (hDt : D (algebraMap B K t) = 1) :
    ∃ c0 c1 : B, (IsUnit c0 ∨ IsUnit c1) ∧
      algebraMap B K c0 = section0 D (algebraMap B K t) ∧
      algebraMap B K c1 = section1 D (algebraMap B K t) := by
  obtain ⟨b0,b1,hu,h0,h1⟩ := regular_derivation_integrality D t ht hDt
  exact scale_integral_pair D _ ⟨b0,b1,Or.inl hu,h0,h1⟩

end SourceHorizontalSections318
