module
public import VerticalSection318
public section
noncomputable section
namespace KilledUniformizerSections318
open VerticalSection318
set_option maxHeartbeats 400000
variable {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Field K] [Algebra R K] [Algebra B K] [IsFractionRing B K]
local notation "v" => ValuationRing.valuation B K

/-- The source vertical estimates with the actual base uniformizer. This
parameter need not equal a rational prime after ramified base change. -/
theorem derivative_contact (D : Derivation R K K)
    (hD : VerticalDerivation318.PreservesIntegral (B := B) D)
    (pi : B) (hpi : Irreducible pi)
    (hkill : D (algebraMap B K pi) = 0) (t : K) (i : Fin 4) :
    v (D t) ≤ v (t - (contacts i : K)) := by
  have h := VerticalDerivation318.canonical_valuation_bound D hD pi hpi hkill
    (t - (contacts i : K))
  simpa only [D.map_sub, D.map_intCast, sub_zero] using h

theorem numerator_bound (D : Derivation R K K)
    (hD : VerticalDerivation318.PreservesIntegral (B := B) D)
    (pi : B) (hpi : Irreducible pi)
    (hkill : D (algebraMap B K pi) = 0) (t : K) :
    v (J : K)^2 * v (D t)^2 ≤ v (denominator t) := by
  have h := four_factor_bound
    (v (t - (contacts 0 : K))) (v (t - (contacts 1 : K)))
    (v (t - (contacts 2 : K))) (v (t - (contacts 3 : K))) (v (D t)) (v (J : K))
    (derivative_contact D hD pi hpi hkill t 0) (derivative_contact D hD pi hpi hkill t 1)
    (derivative_contact D hD pi hpi hkill t 2) (derivative_contact D hD pi hpi hkill t 3)
    (contact_separation t 0 2 (by decide)) (contact_separation t 0 3 (by decide))
    (contact_separation t 1 2 (by decide)) (contact_separation t 1 3 (by decide))
  simpa [denominator, Fin.prod_univ_four, map_mul, mul_assoc] using h

theorem section0_le_one (D : Derivation R K K)
    (hD : VerticalDerivation318.PreservesIntegral (B := B) D)
    (pi : B) (hpi : Irreducible pi)
    (hkill : D (algebraMap B K pi) = 0) (t : K) : v (section0 D t) ≤ 1 := by
  rw [section0, (v).map_div, map_mul, map_pow, map_pow]
  exact div_le_one_of_le₀ (numerator_bound D hD pi hpi hkill t) zero_le

theorem section1_le_one (D : Derivation R K K)
    (hD : VerticalDerivation318.PreservesIntegral (B := B) D)
    (pi : B) (hpi : Irreducible pi)
    (hkill : D (algebraMap B K pi) = 0) (t : K) : v (section1 D t) ≤ 1 := by
  by_cases ht : v t ≤ 1
  · rw [section1, map_mul]
    have hs := section0_le_one D hD pi hpi hkill t
    calc
      v t * v (section0 D t) ≤ 1 * v (section0 D t) := mul_le_mul_left ht _
      _ ≤ 1 * 1 := by gcongr
      _ = _ := one_mul _
  · have ht' : 1 < v t := lt_of_not_ge ht
    have hd : v (D t) ≤ v t := by
      simpa [contacts] using derivative_contact D hD pi hpi hkill t 0
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
    (pi : B) (hpi : Irreducible pi)
    (hkill : D (algebraMap B K pi) = 0) (t : K) :
    (∃ b : B, algebraMap B K b = section0 D t) ∧
    (∃ b : B, algebraMap B K b = section1 D t) := by
  constructor
  · exact (ValuationRing.integers B K).exists_of_le_one (section0_le_one D hD pi hpi hkill t)
  · exact (ValuationRing.integers B K).exists_of_le_one (section1_le_one D hD pi hpi hkill t)

end KilledUniformizerSections318
