module
public import DVRFractionCharacterParity318
public section
noncomputable section
namespace QuadraticLocalCharacterOrders318
open RationalFunctionEvenSquare318 PolynomialPrimeValuation318 DVRFractionCharacterParity318
open IsLocalRing
variable {R K F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Field F] [Algebra (RatFunc F) K]

/-- At an actual unramified DVR, the square equation forces even base order.
The full restriction map of valuations, not an asserted parity, is consumed. -/
theorem unramified (q : Polynomial F) (hq : Prime q)
    (hrestrict : ∀ a : RatFunc F, a ≠ 0 →
      value R K (algebraMap (RatFunc F) K a) = primePlace q hq a)
    (a : RatFunc F) (ha : a ≠ 0) (y : K) (hy : y ^ 2 = algebraMap (RatFunc F) K a) :
    Even (orderAt q a) := by
  have hyn : y ≠ 0 := by
    intro h
    have hmap : algebraMap (RatFunc F) K a ≠ 0 := by
      simpa only [map_zero] using (algebraMap (RatFunc F) K).injective.ne ha
    apply hmap
    simpa [h] using hy.symm
  obtain ⟨n, hn⟩ := value_finite R K y hyn
  have hh := congrArg (value R K) hy
  rw [(value R K).map_pow, hn, hrestrict a ha, primePlace_order q hq a ha,
    two_nsmul] at hh
  have he : n + n = orderAt q a := by exact_mod_cast hh
  exact ⟨n, he.symm⟩

variable [CharZero (ResidueField R)]
/-- At an actual index2 DVR the base order of a quadratic radicand has exactly
the sign parity of its ORIGINAL local inertia action, even when the chosen
character function has a pole. -/
theorem ramified (q : Polynomial F) (hq : Prime q)
    (hrestrict : ∀ a : RatFunc F, a ≠ 0 →
      value R K (algebraMap (RatFunc F) K a) = 2 • primePlace q hq a)
    (τ : R ≃+* R) (σ : K ≃+* K)
    (hcompat : ∀ x : R, σ (algebraMap R K x) = algebraMap R K (τ x))
    (hres : ∀ x : R, residue R (τ x) = residue R x)
    (π : R) (hπ : Irreducible π) (hτπ : τ π = -π)
    (a : RatFunc F) (ha : a ≠ 0) (y : K) (hy : y ^ 2 = algebraMap (RatFunc F) K a)
    (b : Bool) (hσy : σ y = (if b then -1 else 1) * y) :
    Even (orderAt q a) ↔ b = false := by
  have hyn : y ≠ 0 := by
    intro h
    have hmap : algebraMap (RatFunc F) K a ≠ 0 := by
      simpa only [map_zero] using (algebraMap (RatFunc F) K).injective.ne ha
    apply hmap
    simpa [h] using hy.symm
  obtain ⟨n, hn, hp⟩ := eigenvalue_order R K τ σ hcompat hres π hπ hτπ y hyn b hσy
  have hh := congrArg (value R K) hy
  rw [(value R K).map_pow, hn, hrestrict a ha, primePlace_order q hq a ha,
    two_nsmul, two_nsmul] at hh
  have he : n + n = orderAt q a + orderAt q a := by exact_mod_cast hh
  have hnm : n = orderAt q a := by omega
  exact hnm ▸ hp
end QuadraticLocalCharacterOrders318
