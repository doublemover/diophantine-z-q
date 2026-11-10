module
public import PolynomialPrimeValuation318
public import DVRInertiaCharacterParity318
public import Mathlib.RingTheory.Valuation.ValuationRing
public section
noncomputable section
namespace DVRFractionCharacterParity318
open IsDiscreteValuationRing IsLocalRing
variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

@[expose] def integralValue : AddValuation R (WithTop ℤ) :=
  (addVal R).map PolynomialPrimeValuation318.enatToInt rfl

lemma integralValue_finite (x : R) (hx : x ≠ 0) :
    integralValue R x = ((addVal R x).toNat : ℤ) := by
  have htop : addVal R x ≠ ⊤ := fun h => hx ((addVal_eq_top_iff (R := R)).mp h)
  change PolynomialPrimeValuation318.enatToInt (addVal R x) = _
  rw [← ENat.natCast_toNat htop]
  all_goals rfl

lemma support : nonZeroDivisors R ≤
    (AddValuation.toValuation (integralValue R)).supp.primeCompl := by
  intro x hx
  have hn : x ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hx
  change integralValue R x ≠ ⊤
  rw [integralValue_finite R x hn]
  simp

/-- The canonical additive DVR valuation on its ORIGINAL fraction field. -/
@[expose] def value : AddValuation K (WithTop ℤ) :=
  AddValuation.ofValuation ((AddValuation.toValuation (integralValue R)).extendToLocalization
    (support R) K)

lemma value_integral (x : R) (hx : x ≠ 0) :
    value R K (algebraMap R K x) = ((addVal R x).toNat : ℤ) := by
  change (AddValuation.toValuation (integralValue R)).extendToLocalization
    (support R) K (algebraMap R K x) = _
  rw [Valuation.extendToLocalization_apply_map_apply]
  exact integralValue_finite R x hx

/-- The actual valuation-ring property covers poles as well as regular elements. -/
theorem value_finite (y : K) (hy : y ≠ 0) : ∃ n : ℤ, value R K y = n := by
  rcases ValuationRing.isInteger_or_isInteger R y with ⟨x, hx⟩ | ⟨x, hx⟩
  · have hxn : x ≠ 0 := by intro h; apply hy; simpa [h] using hx.symm
    exact ⟨(addVal R x).toNat, hx ▸ value_integral R K x hxn⟩
  · have hxn : x ≠ 0 := by intro h; apply inv_ne_zero hy; simpa [h] using hx.symm
    refine ⟨-((addVal R x).toNat : ℤ), ?_⟩
    have he := value_integral R K x hxn
    rw [hx, (value R K).map_inv] at he
    have hh := congrArg Neg.neg he
    simpa only [neg_neg, WithTop.coe_neg] using hh

variable [CharZero (ResidueField R)]

/-- The entire fraction field, including poles, has valuation parity dictated
by the actual inertia sign. Actual restriction of the field automorphism to
the local ring and identity on its full residue field are both required. -/
theorem eigenvalue_order (τ : R ≃+* R) (σ : K ≃+* K)
    (hcompat : ∀ x : R, σ (algebraMap R K x) = algebraMap R K (τ x))
    (hres : ∀ x : R, residue R (τ x) = residue R x)
    (π : R) (hπ : Irreducible π) (hτπ : τ π = -π)
    (y : K) (hy : y ≠ 0) (b : Bool) (hσy : σ y = (if b then -1 else 1) * y) :
    ∃ n : ℤ, value R K y = n ∧ (Even n ↔ b = false) := by
  have integral_case : ∀ (z : K), z ≠ 0 → σ z = (if b then -1 else 1) * z →
      ∀ x : R, algebraMap R K x = z →
        ∃ n : ℤ, value R K z = n ∧ (Even n ↔ b = false) := by
    intro z hz hσz x hx
    have hxn : x ≠ 0 := by intro h; apply hz; simpa [h] using hx.symm
    have hτx : τ x = (if b then -1 else 1) * x := by
      apply IsFractionRing.injective R K
      rw [← hcompat, map_mul, hx, hσz]
      cases b <;> simp
    refine ⟨(addVal R x).toNat, hx ▸ value_integral R K x hxn, ?_⟩
    exact_mod_cast DVRInertiaCharacterParity318.order_even_iff τ hres π hπ hτπ x hxn b hτx
  rcases ValuationRing.isInteger_or_isInteger R y with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact integral_case y hy hσy x hx
  · have hinv : σ y⁻¹ = (if b then -1 else 1) * y⁻¹ := by
      cases b <;> simp_all
    obtain ⟨n, hn, hp⟩ := integral_case y⁻¹ (inv_ne_zero hy) hinv x hx
    refine ⟨-n, ?_, by simpa using hp⟩
    rw [(value R K).map_inv] at hn
    have hh := congrArg Neg.neg hn
    simpa only [neg_neg, WithTop.coe_neg] using hh
end DVRFractionCharacterParity318
