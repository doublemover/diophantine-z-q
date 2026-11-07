module
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace VerticalDerivation318
open IsDiscreteValuationRing
set_option maxHeartbeats 0
variable {R B K : Type*} [CommRing R] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Field K] [Algebra R K] [Algebra B K] [IsFractionRing B K]

/-- Actual preservation of the integral lattice in a differential frame. -/
@[expose] def PreservesIntegral (D : Derivation R K K) : Prop :=
  ∀ b : B, ∃ c : B, D (algebraMap B K b) = algebraMap B K c

/-- The derivative of every integer power of a killed uniformizer vanishes,
including negative powers in the actual fraction field. -/
theorem killed_zpow (D : Derivation R K K) (pi : B)
    (hpi : D (algebraMap B K pi) = 0) (n : ℤ) :
    D ((algebraMap B K pi)^n) = 0 := by
  rw [D.leibniz_zpow, hpi]
  simp

/-- In a reduced vertical DVR, the derivative of any fraction is its own
multiple by an integral coefficient.  The unit/power expression is obtained
from the actual DVR fraction-field theorem, not supplied as a decomposition. -/
theorem derivative_integral_multiple (D : Derivation R K K)
    (hD : PreservesIntegral (B := B) D) (pi : B) (hirr : Irreducible pi)
    (hpi : D (algebraMap B K pi) = 0) (x : K) :
    ∃ b : B, D x = algebraMap B K b * x := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, by simp⟩
  obtain ⟨n, u, hu⟩ := exists_units_eq_smul_zpow_of_irreducible hirr hx
  obtain ⟨du, hdu⟩ := hD (u : B)
  refine ⟨du * (↑(u⁻¹) : B), ?_⟩
  have hunit : algebraMap B K (↑(u⁻¹) : B) * algebraMap B K (u : B) = 1 := by
    rw [←map_mul]
    simp
  simp only [Units.smul_def, Algebra.smul_def] at hu
  rw [hu, D.leibniz, killed_zpow D pi hpi n, smul_zero, zero_add, hdu,
    smul_eq_mul, map_mul]
  calc
    (algebraMap B K pi)^n * algebraMap B K du =
        algebraMap B K du * ((algebraMap B K (↑(u⁻¹) : B) *
          algebraMap B K (u : B)) * (algebraMap B K pi)^n) := by rw [hunit]; ring
    _ = _ := by ring

/-- A concrete integral logarithmic derivative, including the zero case. -/
theorem logarithmic_derivative_integral (D : Derivation R K K)
    (hD : PreservesIntegral (B := B) D) (pi : B) (hirr : Irreducible pi)
    (hpi : D (algebraMap B K pi) = 0) (x : K) :
    ∃ b : B, D x / x = algebraMap B K b := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨b, hb⟩ := derivative_integral_multiple D hD pi hirr hpi x
  exact ⟨b, by rw [hb, mul_div_cancel_right₀ _ hx]⟩

/-- The actual canonical DVR valuation decreases multiplicatively under
relative differentiation, equivalent to the source additive order inequality. -/
theorem canonical_valuation_bound (D : Derivation R K K)
    (hD : PreservesIntegral (B := B) D) (pi : B) (hirr : Irreducible pi)
    (hpi : D (algebraMap B K pi) = 0) (x : K) :
    ValuationRing.valuation B K (D x) ≤ ValuationRing.valuation B K x := by
  obtain ⟨b, hb⟩ := derivative_integral_multiple D hD pi hirr hpi x
  rw [hb, map_mul]
  calc
    _ ≤ 1 * ValuationRing.valuation B K x :=
      mul_le_mul_left ((ValuationRing.integers B K).map_le_one b) _
    _ = _ := one_mul _

/-- Rational-prime uniformizers are killed by the genuine relative derivation;
no zero-derivative assumption is needed for the source specialization. -/
theorem prime_uniformizer_multiple (D : Derivation R K K)
    (hD : PreservesIntegral (B := B) D) (p : ℕ) (hirr : Irreducible (p : B)) (x : K) :
    ∃ b : B, D x = algebraMap B K b * x := by
  apply derivative_integral_multiple D hD (p : B) hirr
  simp only [map_natCast, D.map_natCast]

/-- Exact source vertical derivative bound at a reduced smooth component. -/
theorem prime_uniformizer_valuation (D : Derivation R K K)
    (hD : PreservesIntegral (B := B) D) (p : ℕ) (hirr : Irreducible (p : B)) (x : K) :
    ValuationRing.valuation B K (D x) ≤ ValuationRing.valuation B K x := by
  apply canonical_valuation_bound D hD (p : B) hirr
  simp only [map_natCast, D.map_natCast]

/-- The exact additive-order form for any actual additive valuation whose
integral lattice contains B.  No valuation estimate for a derivative is assumed. -/
theorem additive_valuation_bound {Γ : Type*} [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation K Γ) (hv : ∀ b : B, 0 ≤ v (algebraMap B K b))
    (D : Derivation R K K) (hD : PreservesIntegral (B := B) D)
    (pi : B) (hirr : Irreducible pi) (hpi : D (algebraMap B K pi) = 0) (x : K) :
    v x ≤ v (D x) := by
  obtain ⟨b, hb⟩ := derivative_integral_multiple D hD pi hirr hpi x
  rw [hb, v.map_mul]
  simpa only [zero_add, add_zero, add_comm] using add_le_add_right (hv b) (v x)

/-- The source additive inequality with a rational-prime uniformizer. -/
theorem prime_uniformizer_additive {Γ : Type*} [LinearOrderedAddCommMonoidWithTop Γ]
    (v : AddValuation K Γ) (hv : ∀ b : B, 0 ≤ v (algebraMap B K b))
    (D : Derivation R K K) (hD : PreservesIntegral (B := B) D)
    (p : ℕ) (hirr : Irreducible (p : B)) (x : K) : v x ≤ v (D x) := by
  apply additive_valuation_bound v hv D hD (p : B) hirr
  simp only [map_natCast, D.map_natCast]

/-- In particular the canonical DVR valuation, in additive convention,
has the source's increasing-order direction. -/
theorem canonical_additive_valuation (D : Derivation R K K)
    (hD : PreservesIntegral (B := B) D) (p : ℕ) (hirr : Irreducible (p : B)) (x : K) :
    Valuation.toAddValuation (ValuationRing.valuation B K) x ≤
      Valuation.toAddValuation (ValuationRing.valuation B K) (D x) :=
  prime_uniformizer_valuation D hD p hirr x

end VerticalDerivation318
#print axioms VerticalDerivation318.derivative_integral_multiple
#print axioms VerticalDerivation318.logarithmic_derivative_integral
#print axioms VerticalDerivation318.canonical_valuation_bound
#print axioms VerticalDerivation318.prime_uniformizer_valuation
