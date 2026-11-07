module
public import VerticalDerivation318
public section
noncomputable section
namespace VerticalSection318
set_option maxHeartbeats 0

/-- A four-factor nonarchimedean estimate. The pairwise separation gives
at least two factors large enough to absorb the two copies of J. -/
theorem four_factor_bound {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (a b c d m r : Γ) (ha : m ≤ a) (hb : m ≤ b) (hc : m ≤ c) (hd : m ≤ d)
    (hac : r ≤ max a c) (had : r ≤ max a d)
    (hbc : r ≤ max b c) (hbd : r ≤ max b d) :
    r^2 * m^2 ≤ a*b*c*d := by
  by_cases hr : r ≤ a ∧ r ≤ b
  · rcases hr with ⟨hra,hrb⟩
    calc
      r^2 * m^2 = r*r*m*m := by simp only [pow_two]; ac_rfl
      _ ≤ a*b*c*d := by gcongr
  · have hcd : r ≤ c ∧ r ≤ d := by
      by_cases hra : r ≤ a
      · have hbr : b < r := lt_of_not_ge (fun h => hr ⟨hra,h⟩)
        constructor
        · exact (le_max_iff.mp hbc).resolve_left (not_le_of_gt hbr)
        · exact (le_max_iff.mp hbd).resolve_left (not_le_of_gt hbr)
      · have har : a < r := lt_of_not_ge hra
        constructor
        · exact (le_max_iff.mp hac).resolve_left (not_le_of_gt har)
        · exact (le_max_iff.mp had).resolve_left (not_le_of_gt har)
    rcases hcd with ⟨hrc,hrd⟩
    calc
      r^2 * m^2 = m*m*r*r := by simp only [pow_two]; ac_rfl
      _ ≤ a*b*c*d := by gcongr

@[expose] def contacts : Fin 4 → ℤ := ![0,32,76832,-343]
@[expose] def J : ℤ := 2765952000

theorem difference_dvd_J (i j : Fin 4) (hij : i ≠ j) : contacts i - contacts j ∣ J := by
  fin_cases i <;> fin_cases j <;> norm_num [contacts,J] at *

variable {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Field K] [Algebra R K] [Algebra B K] [IsFractionRing B K]

local notation "v" => ValuationRing.valuation B K

theorem integer_le_one (n : ℤ) : v (n : K) ≤ 1 := by
  simpa using (ValuationRing.integers B K).map_le_one (n : B)

theorem difference_lower (i j : Fin 4) (hij : i ≠ j) :
    v (J : K) ≤ v ((contacts i : K) - (contacts j : K)) := by
  obtain ⟨c,hc⟩ := difference_dvd_J i j hij
  have he : (J : K) = ((contacts i : K) - (contacts j : K)) * (c : K) := by
    simpa only [Int.cast_mul, Int.cast_sub] using congrArg (fun z : ℤ => (z : K)) hc
  rw [he, map_mul]
  calc
    _ ≤ v ((contacts i : K) - (contacts j : K)) * 1 := by gcongr; exact integer_le_one c
    _ = _ := mul_one _

theorem contact_separation (t : K) (i j : Fin 4) (hij : i ≠ j) :
    v (J : K) ≤ max (v (t - (contacts i : K))) (v (t - (contacts j : K))) := by
  calc
    _ ≤ v ((contacts i : K) - (contacts j : K)) := difference_lower i j hij
    _ = v ((t - (contacts j : K)) - (t - (contacts i : K))) := by congr 1; ring
    _ ≤ max (v (t - (contacts j : K))) (v (t - (contacts i : K))) := (v).map_sub _ _
    _ = _ := max_comm _ _

theorem derivative_contact (D : Derivation R K K)
    (hD : VerticalDerivation318.PreservesIntegral (B := B) D)
    (p : ℕ) (hp : Irreducible (p : B)) (t : K) (i : Fin 4) :
    v (D t) ≤ v (t - (contacts i : K)) := by
  have h := VerticalDerivation318.prime_uniformizer_valuation D hD p hp
    (t - (contacts i : K))
  simpa only [D.map_sub, D.map_intCast, sub_zero] using h

@[expose] def denominator (t : K) : K := ∏ i : Fin 4, (t - (contacts i : K))
@[expose] def section0 (D : Derivation R K K) (t : K) : K :=
  (J : K)^2 * (D t)^2 / denominator t
@[expose] def section1 (D : Derivation R K K) (t : K) : K := t * section0 D t

theorem numerator_bound (D : Derivation R K K)
    (hD : VerticalDerivation318.PreservesIntegral (B := B) D)
    (p : ℕ) (hp : Irreducible (p : B)) (t : K) :
    v (J : K)^2 * v (D t)^2 ≤ v (denominator t) := by
  have h := four_factor_bound
    (v (t - (contacts 0 : K))) (v (t - (contacts 1 : K)))
    (v (t - (contacts 2 : K))) (v (t - (contacts 3 : K))) (v (D t)) (v (J : K))
    (derivative_contact D hD p hp t 0) (derivative_contact D hD p hp t 1)
    (derivative_contact D hD p hp t 2) (derivative_contact D hD p hp t 3)
    (contact_separation t 0 2 (by decide)) (contact_separation t 0 3 (by decide))
    (contact_separation t 1 2 (by decide)) (contact_separation t 1 3 (by decide))
  simpa [denominator, Fin.prod_univ_four, map_mul, mul_assoc] using h

theorem section0_le_one (D : Derivation R K K)
    (hD : VerticalDerivation318.PreservesIntegral (B := B) D)
    (p : ℕ) (hp : Irreducible (p : B)) (t : K) : v (section0 D t) ≤ 1 := by
  rw [section0, (v).map_div, map_mul, map_pow, map_pow]
  exact div_le_one_of_le₀ (numerator_bound D hD p hp t) zero_le

theorem section1_le_one (D : Derivation R K K)
    (hD : VerticalDerivation318.PreservesIntegral (B := B) D)
    (p : ℕ) (hp : Irreducible (p : B)) (t : K) : v (section1 D t) ≤ 1 := by
  by_cases ht : v t ≤ 1
  · rw [section1, map_mul]
    have hs := section0_le_one D hD p hp t
    calc
      v t * v (section0 D t) ≤ 1 * v (section0 D t) := mul_le_mul_left ht _
      _ ≤ 1 * 1 := by gcongr
      _ = _ := one_mul _
  · have ht' : 1 < v t := lt_of_not_ge ht
    have hd : v (D t) ≤ v t := by
      simpa [contacts] using derivative_contact D hD p hp t 0
    have hc (i : Fin 4) : v (t - (contacts i : K)) = v t :=
      (v).map_sub_eq_of_lt_left ((integer_le_one (contacts i)).trans_lt ht')
    have hden : v (denominator t) = (v t)^4 := by
      simp only [denominator, Fin.prod_univ_four, map_mul, hc]
      simp only [pow_succ, pow_zero, one_mul]
    have hn : v t * v (J : K)^2 * v (D t)^2 ≤ (v t)^4 := by
      calc
        _ ≤ v t * 1^2 * (v t)^2 := by gcongr; exact integer_le_one J
        _ = (v t)^3 * 1 := by simp only [mul_one, pow_succ, pow_zero, one_mul]; ac_rfl
        _ ≤ (v t)^3 * v t := by gcongr
        _ = (v t)^4 := by simp only [pow_succ]
    rw [section1, section0, map_mul, (v).map_div, map_mul, map_pow, map_pow, hden,
      ←mul_div_assoc, ←mul_assoc]
    exact div_le_one_of_le₀ hn zero_le

/-- The two literal J-squared scaled bicanonical coefficients are elements of
this actual vertical DVR. No derivative inequality or contact-order bound is
assumed; both are derived from the genuine derivation and fixed contacts. -/
theorem sections_integral (D : Derivation R K K)
    (hD : VerticalDerivation318.PreservesIntegral (B := B) D)
    (p : ℕ) (hp : Irreducible (p : B)) (t : K) :
    (∃ b : B, algebraMap B K b = section0 D t) ∧
    (∃ b : B, algebraMap B K b = section1 D t) := by
  constructor
  · exact (ValuationRing.integers B K).exists_of_le_one (section0_le_one D hD p hp t)
  · exact (ValuationRing.integers B K).exists_of_le_one (section1_le_one D hD p hp t)

/-- The exact denominator of the published finite-contact quadratic differential. -/
theorem denominator_literal (t : K) :
    denominator t = t * (t-32) * (t-76832) * (t+343) := by
  simp [denominator, Fin.prod_univ_four, contacts]

/-- Literal published coefficients, not an abstract height or valuation model. -/
theorem literal_sections_integral (D : Derivation R K K)
    (hD : VerticalDerivation318.PreservesIntegral (B := B) D)
    (p : ℕ) (hp : Irreducible (p : B)) (t : K) :
    (∃ b : B, algebraMap B K b =
      (2765952000 : K)^2 * (D t)^2 / (t*(t-32)*(t-76832)*(t+343))) ∧
    (∃ b : B, algebraMap B K b =
      t * ((2765952000 : K)^2 * (D t)^2 / (t*(t-32)*(t-76832)*(t+343)))) := by
  simpa only [section1, section0, denominator_literal, J, Int.cast_ofNat] using
    sections_integral D hD p hp t

end VerticalSection318
