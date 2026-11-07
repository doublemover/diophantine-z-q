module
public import AlgebraicSectionPullback318
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public section
noncomputable section
namespace HorizontalIntegralCharts318
open VerticalSection318 AlgebraicSectionPullback318 IsLocalRing
set_option maxHeartbeats 0
variable {B K : Type*} [CommRing B] [IsLocalRing B] [Algebra ℚ B]

theorem integer_isUnit (n : ℤ) (hn : n ≠ 0) : IsUnit (n : B) := by
  have hq : IsUnit (n : ℚ) := isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hn)
  simpa only [map_intCast] using hq.map (algebraMap ℚ B)

theorem difference_isUnit (i j : Fin 4) (hij : i ≠ j) :
    IsUnit ((contacts i : B) - (contacts j : B)) := by
  have hn : contacts i - contacts j ≠ 0 := by
    fin_cases i <;> fin_cases j <;> norm_num [contacts] at *
  simpa only [Int.cast_sub] using integer_isUnit (B := B) (contacts i - contacts j) hn

/-- At a horizontal branch, distinct rational contacts give actual unit
factors in the local ring; this is not an assumed holomorphy statement. -/
theorem branchDen_isUnit (i : Fin 4) (z : B) (hz : z ∈ maximalIdeal B) :
    IsUnit (branchDen i z) := by
  apply IsUnit.prod_univ_iff.mpr
  intro j
  apply (residue_ne_zero_iff_isUnit _).mp
  have hr : residue B z = 0 := (residue_eq_zero_iff z).mpr hz
  simp only [map_add, map_sub, map_pow, hr, zero_pow (by decide : 2 ≠ 0), add_zero]
  exact ((difference_isUnit i j (Ne.symm j.property)).map (residue B)).ne_zero

/-- Every infinity factor has residue one, at every horizontal local point. -/
theorem infinityDen_isUnit (z : B) (hz : z ∈ maximalIdeal B) :
    IsUnit (infinityDen z) := by
  apply IsUnit.prod_univ_iff.mpr
  intro j
  apply (residue_ne_zero_iff_isUnit _).mp
  have hr : residue B z = 0 := (residue_eq_zero_iff z).mpr hz
  simp [hr]

variable [Field K] [Algebra B K]

theorem map_branchDen (i : Fin 4) (z : B) :
    algebraMap B K (branchDen i z) = branchDen i (algebraMap B K z) := by
  simp [branchDen]

theorem map_infinityDen (z : B) :
    algebraMap B K (infinityDen z) = infinityDen (algebraMap B K z) := by
  simp [infinityDen]

/-- Both actual finite-branch coefficients lift to B, and the first is a unit.
This proves no common zero in the algebraic horizontal chart. -/
theorem branch_coefficients (i : Fin 4) (z : B) (hz : z ∈ maximalIdeal B) :
    ∃ b0 b1 : B, IsUnit b0 ∧
      algebraMap B K b0 = 4 / branchDen i (algebraMap B K z) ∧
      algebraMap B K b1 = ((contacts i : K) + (algebraMap B K z)^2) *
        (4 / branchDen i (algebraMap B K z)) := by
  obtain ⟨u,hu⟩ := branchDen_isUnit i z hz
  have hmap : algebraMap B K (u : B) = branchDen i (algebraMap B K z) := by
    rw [hu, map_branchDen]
  have hinv : algebraMap B K (↑(u⁻¹) : B) = (branchDen i (algebraMap B K z))⁻¹ := by
    rw [map_units_inv, hmap]
  let b0 : B := 4 * (↑(u⁻¹) : B)
  have h0 : algebraMap B K b0 = 4 / branchDen i (algebraMap B K z) := by
    simp only [b0, map_mul, map_ofNat, hinv, div_eq_mul_inv]
  refine ⟨b0, ((contacts i : B) + z^2)*b0, ?_, h0, ?_⟩
  · simpa only [b0, Int.cast_ofNat] using (integer_isUnit (B := B) 4 (by norm_num)).mul (u⁻¹).isUnit
  · simp only [map_mul, map_add, map_intCast, map_pow, h0]

/-- At infinity the second actual coefficient is a unit, while the first has
its exact z-squared zero. No common-zero conclusion is supplied as a premise. -/
theorem infinity_coefficients (z : B) (hz : z ∈ maximalIdeal B) :
    ∃ b0 b1 : B, IsUnit b1 ∧
      algebraMap B K b0 = 4*(algebraMap B K z)^2 / infinityDen (algebraMap B K z) ∧
      algebraMap B K b1 = 4 / infinityDen (algebraMap B K z) ∧ b0 = z^2*b1 := by
  obtain ⟨u,hu⟩ := infinityDen_isUnit z hz
  have hmap : algebraMap B K (u : B) = infinityDen (algebraMap B K z) := by
    rw [hu, map_infinityDen]
  have hinv : algebraMap B K (↑(u⁻¹) : B) = (infinityDen (algebraMap B K z))⁻¹ := by
    rw [map_units_inv, hmap]
  let b1 : B := 4 * (↑(u⁻¹) : B)
  have h1 : algebraMap B K b1 = 4 / infinityDen (algebraMap B K z) := by
    simp only [b1, map_mul, map_ofNat, hinv, div_eq_mul_inv]
  refine ⟨z^2*b1, b1, ?_, ?_, h1, rfl⟩
  · simpa only [b1, Int.cast_ofNat] using (integer_isUnit (B := B) 4 (by norm_num)).mul (u⁻¹).isUnit
  · simp only [map_mul, map_pow, h1]
    ring

/-- Off the branch divisor, residue separation gives a unit first coefficient. -/
theorem regular_coefficients (t : B)
    (ht : ∀ i : Fin 4, residue B t ≠ residue B (contacts i : B)) :
    ∃ b0 b1 : B, IsUnit b0 ∧
      algebraMap B K b0 = 1 / denominator (algebraMap B K t) ∧
      algebraMap B K b1 = algebraMap B K t * (1 / denominator (algebraMap B K t)) := by
  have hd : IsUnit (∏ i : Fin 4, (t - (contacts i : B))) := by
    apply IsUnit.prod_univ_iff.mpr
    intro i
    apply (residue_ne_zero_iff_isUnit _).mp
    simpa only [map_sub, sub_ne_zero] using ht i
  obtain ⟨u,hu⟩ := hd
  have hmap : algebraMap B K (u : B) = denominator (algebraMap B K t) := by
    rw [hu]
    simp [denominator]
  have hinv : algebraMap B K (↑(u⁻¹) : B) = (denominator (algebraMap B K t))⁻¹ := by
    rw [map_units_inv, hmap]
  refine ⟨(↑(u⁻¹) : B), t*(↑(u⁻¹) : B), (u⁻¹).isUnit, ?_, ?_⟩
  · simpa only [one_div] using hinv
  · simp only [map_mul, hinv, one_div]

variable {R : Type*} [CommRing R] [Algebra R K] [IsDomain B] [IsFractionRing B K]

/-- Actual D-based coefficients in a finite horizontal branch frame. -/
theorem finite_derivation_integrality (D : Derivation R K K) (i : Fin 4) (z : B)
    (hz : z ∈ maximalIdeal B) (hz0 : z ≠ 0) (hDz : D (algebraMap B K z) = 1) :
    ∃ b0 b1 : B, IsUnit b0 ∧
      algebraMap B K b0 = coefficient0 D ((contacts i : K) + (algebraMap B K z)^2) ∧
      algebraMap B K b1 = coefficient1 D ((contacts i : K) + (algebraMap B K z)^2) := by
  have hzK : algebraMap B K z ≠ 0 := fun h => hz0 ((IsFractionRing.injective B K) (by simpa using h))
  obtain ⟨h0,h1⟩ := finite_coordinate_coefficients D i (algebraMap B K z) hzK hDz
  rw [h0,h1]
  exact branch_coefficients i z hz

/-- Actual D-based coefficients in the infinity horizontal frame. -/
theorem infinity_derivation_integrality (D : Derivation R K K) (z : B)
    (hz : z ∈ maximalIdeal B) (hz0 : z ≠ 0) (hDz : D (algebraMap B K z) = 1) :
    ∃ b0 b1 : B, IsUnit b1 ∧
      algebraMap B K b0 = coefficient0 D (1 / (algebraMap B K z)^2) ∧
      algebraMap B K b1 = coefficient1 D (1 / (algebraMap B K z)^2) := by
  have hzK : algebraMap B K z ≠ 0 := fun h => hz0 ((IsFractionRing.injective B K) (by simpa using h))
  obtain ⟨h0,h1⟩ := infinity_coordinate_coefficients D (algebraMap B K z) hzK hDz
  rw [h0,h1]
  obtain ⟨b0,b1,hb1,hb0,hb1',-⟩ := infinity_coefficients (K := K) z hz
  exact ⟨b0,b1,hb1,hb0,hb1'⟩

theorem regular_derivation_integrality (D : Derivation R K K) (t : B)
    (ht : ∀ i : Fin 4, residue B t ≠ residue B (contacts i : B))
    (hDt : D (algebraMap B K t) = 1) :
    ∃ b0 b1 : B, IsUnit b0 ∧
      algebraMap B K b0 = coefficient0 D (algebraMap B K t) ∧
      algebraMap B K b1 = coefficient1 D (algebraMap B K t) := by
  simpa only [coefficient1, coefficient0, hDt, one_pow] using regular_coefficients (K := K) t ht

end HorizontalIntegralCharts318
