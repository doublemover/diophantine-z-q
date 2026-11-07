module
public import SourceHorizontalSections318
public section
noncomputable section
namespace UnitFrameHorizontal318
open VerticalSection318 AlgebraicSectionPullback318 HorizontalIntegralCharts318
open SourceHorizontalSections318 IsLocalRing
set_option maxHeartbeats 0
variable {R B K : Type*} [CommRing R] [CommRing B] [IsLocalRing B] [Algebra ℚ B]
  [Field K] [Algebra B K] [Algebra R K]

/-- Changing an integral cotangent frame by an actual unit preserves integral
quadratic coefficients and the absence of a common zero. -/
theorem unit_square_pair (u : B) (hu : IsUnit u) (x0 x1 : K)
    (h : ∃ b0 b1 : B, (IsUnit b0 ∨ IsUnit b1) ∧
      algebraMap B K b0 = x0 ∧ algebraMap B K b1 = x1) :
    ∃ c0 c1 : B, (IsUnit c0 ∨ IsUnit c1) ∧
      algebraMap B K c0 = (algebraMap B K u)^2*x0 ∧
      algebraMap B K c1 = (algebraMap B K u)^2*x1 := by
  obtain ⟨b0,b1,hunit,h0,h1⟩ := h
  refine ⟨u^2*b0,u^2*b1,hunit.imp ((hu.pow 2).mul ·) ((hu.pow 2).mul ·),?_,?_⟩
  · rw [map_mul,map_pow,h0]
  · rw [map_mul,map_pow,h1]

variable [IsDomain B] [IsFractionRing B K]

/-- Finite branch in any integral frame with unit dz coefficient, rather than
only the normalized Dz=1 frame. -/
theorem finite_branch_sections (D : Derivation R K K) (i : Fin 4) (z u : B)
    (hz : z ∈ maximalIdeal B) (hz0 : z ≠ 0) (hu : IsUnit u)
    (hDz : D (algebraMap B K z) = algebraMap B K u) :
    ∃ c0 c1 : B, (IsUnit c0 ∨ IsUnit c1) ∧
      algebraMap B K c0 = section0 D ((contacts i : K) + (algebraMap B K z)^2) ∧
      algebraMap B K c1 = section1 D ((contacts i : K) + (algebraMap B K z)^2) := by
  apply scale_integral_pair
  have hzK : algebraMap B K z ≠ 0 := fun h => hz0 ((IsFractionRing.injective B K) (by simpa using h))
  have h0 : coefficient0 D ((contacts i : K) + (algebraMap B K z)^2) =
      (algebraMap B K u)^2 * (4 / branchDen i (algebraMap B K z)) := by
    rw [finite_coefficient0 D i _ hzK,hDz]
    ring
  have h1 : coefficient1 D ((contacts i : K) + (algebraMap B K z)^2) =
      (algebraMap B K u)^2 * (((contacts i : K) + (algebraMap B K z)^2) *
        (4 / branchDen i (algebraMap B K z))) := by
    rw [finite_coefficient1 D i _ hzK,hDz]
    ring
  rw [h0,h1]
  apply unit_square_pair u hu
  obtain ⟨b0,b1,hb,hb0,hb1⟩ := branch_coefficients (K := K) i z hz
  exact ⟨b0,b1,Or.inl hb,hb0,hb1⟩

/-- Infinity in an arbitrary integral differential frame. -/
theorem infinity_sections (D : Derivation R K K) (z u : B)
    (hz : z ∈ maximalIdeal B) (hz0 : z ≠ 0) (hu : IsUnit u)
    (hDz : D (algebraMap B K z) = algebraMap B K u) :
    ∃ c0 c1 : B, (IsUnit c0 ∨ IsUnit c1) ∧
      algebraMap B K c0 = section0 D (1 / (algebraMap B K z)^2) ∧
      algebraMap B K c1 = section1 D (1 / (algebraMap B K z)^2) := by
  apply scale_integral_pair
  have hzK : algebraMap B K z ≠ 0 := fun h => hz0 ((IsFractionRing.injective B K) (by simpa using h))
  have h0 : coefficient0 D (1 / (algebraMap B K z)^2) =
      (algebraMap B K u)^2 * (4*(algebraMap B K z)^2 / infinityDen (algebraMap B K z)) := by
    rw [infinity_coefficient0 D _ hzK,hDz]
    ring
  have h1 : coefficient1 D (1 / (algebraMap B K z)^2) =
      (algebraMap B K u)^2 * (4 / infinityDen (algebraMap B K z)) := by
    rw [infinity_coefficient1 D _ hzK,hDz]
    ring
  rw [h0,h1]
  apply unit_square_pair u hu
  obtain ⟨b0,b1,hb,hb0,hb1,-⟩ := infinity_coefficients (K := K) z hz
  exact ⟨b0,b1,Or.inr hb,hb0,hb1⟩

/-- An ordinary unramified chart in an arbitrary integral differential frame. -/
theorem regular_sections (D : Derivation R K K) (t u : B)
    (ht : ∀ i : Fin 4, residue B t ≠ residue B (contacts i : B))
    (hu : IsUnit u) (hDt : D (algebraMap B K t) = algebraMap B K u) :
    ∃ c0 c1 : B, (IsUnit c0 ∨ IsUnit c1) ∧
      algebraMap B K c0 = section0 D (algebraMap B K t) ∧
      algebraMap B K c1 = section1 D (algebraMap B K t) := by
  apply scale_integral_pair
  have h0 : coefficient0 D (algebraMap B K t) =
      (algebraMap B K u)^2 * (1 / denominator (algebraMap B K t)) := by
    rw [coefficient0,hDt]
    ring
  have h1 : coefficient1 D (algebraMap B K t) =
      (algebraMap B K u)^2 * (algebraMap B K t * (1 / denominator (algebraMap B K t))) := by
    rw [coefficient1,h0]
    ring
  rw [h0,h1]
  apply unit_square_pair u hu
  obtain ⟨b0,b1,hb,hb0,hb1⟩ := regular_coefficients (K := K) t ht
  exact ⟨b0,b1,Or.inl hb,hb0,hb1⟩

end UnitFrameHorizontal318
