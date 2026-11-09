module
public import DVRFractionCharacterParity318
public section
noncomputable section
namespace CenteredDVRRestriction318
open Polynomial IsLocalRing IsDiscreteValuationRing
open DVRFractionCharacterParity318 PolynomialPrimeValuation318 RationalFunctionEvenSquare318
variable {F R L : Type*} [Field F] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra R L] [IsFractionRing R L] [Algebra (RatFunc F) L]
  (q : F[X]) (hq : Prime q) (f : F[X] →+* R)
  (hcompat : ∀ P, algebraMap R L (f P) =
    algebraMap (RatFunc F) L (algebraMap F[X] (RatFunc F) P))
  (hcenter : ∀ P, residue R (f P) = 0 ↔ q ∣ P)

include hcompat in
lemma coefficient_ne_zero (P : F[X]) (hP : P ≠ 0) : f P ≠ 0 := by
  have hn := (algebraMap (RatFunc F) L).injective.ne
    ((IsFractionRing.injective F[X] (RatFunc F)).ne hP)
  intro h
  apply hn
  rw [← hcompat P, h, map_zero]

include hcenter in
lemma prime_unit (P : F[X]) (hP : ¬ q ∣ P) : IsUnit (f P) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  exact fun h => hP ((hcenter P).mp h)

include hcenter in
lemma prime_unit_value (P : F[X]) (hP : ¬ q ∣ P) :
    value R L (algebraMap R L (f P)) = 0 := by
  have hu := prime_unit q f hcenter P hP
  rw [value_integral R L _ hu.ne_zero, (addVal_eq_zero_iff (R := R)).mpr hu]
  all_goals simp

include hq hcompat hcenter in
/-- The actual center identifies polynomial units; the SINGLE canonical
order of q therefore determines the value of every original polynomial. -/
theorem polynomial_value (e : ℕ) (he : addVal R (f q) = e)
    (P : F[X]) (hP : P ≠ 0) :
    value R L (algebraMap (RatFunc F) L (algebraMap F[X] (RatFunc F) P)) =
      (((e : ℤ) * (multiplicity q P : ℤ) : ℤ) : WithTop ℤ) := by
  let n := multiplicity q P
  obtain ⟨s, hfactor, hs⟩ :=
    (FiniteMultiplicity.of_prime_left hq hP).exists_eq_pow_mul_and_not_dvd
  have hqv : value R L (algebraMap R L (f q)) = (e : ℤ) := by
    rw [value_integral R L _ (coefficient_ne_zero f hcompat q hq.ne_zero), he]
    all_goals simp
  have hsv := prime_unit_value (L := L) q f hcenter s hs
  calc
    _ = value R L ((algebraMap R L (f q)) ^ n * algebraMap R L (f s)) := by
      rw [← hcompat P, hfactor, map_mul, map_pow, map_mul, map_pow]
    _ = n • ((e : ℤ) : WithTop ℤ) := by
      rw [(value R L).map_mul, (value R L).map_pow, hqv, hsv, add_zero]
    _ = (((e : ℤ) * (n : ℤ) : ℤ) : WithTop ℤ) := by
      norm_cast
      all_goals simp only [nsmul_eq_mul, mul_comm]

include hq hcompat hcenter in
/-- All original rational functions, including every pole, satisfy the
restriction identity. It is DERIVED from the center and q's single order. -/
theorem rational_value (e : ℕ) (he : addVal R (f q) = e)
    (x : RatFunc F) (hx : x ≠ 0) :
    value R L (algebraMap (RatFunc F) L x) =
      (((e : ℤ) * orderAt q x : ℤ) : WithTop ℤ) := by
  calc
    _ = value R L
        (algebraMap (RatFunc F) L (algebraMap F[X] (RatFunc F) x.num) /
          algebraMap (RatFunc F) L (algebraMap F[X] (RatFunc F) x.denom)) := by
      conv_lhs => rw [← RatFunc.num_div_denom x, map_div₀]
    _ = (((e : ℤ) * (multiplicity q x.num : ℤ) : ℤ) : WithTop ℤ) -
        (((e : ℤ) * (multiplicity q x.denom : ℤ) : ℤ) : WithTop ℤ) := by
      rw [(value R L).map_div,
        polynomial_value q hq f hcompat hcenter e he x.num (RatFunc.num_ne_zero hx),
        polynomial_value q hq f hcompat hcenter e he x.denom (RatFunc.denom_ne_zero x)]
    _ = (((e : ℤ) * orderAt q x : ℤ) : WithTop ℤ) := by
      change (((e : ℤ) * (multiplicity q x.num : ℤ) : ℤ) : WithTop ℤ) -
        (((e : ℤ) * (multiplicity q x.denom : ℤ) : ℤ) : WithTop ℤ) =
        (((e : ℤ) * ((multiplicity q x.num : ℤ) - (multiplicity q x.denom : ℤ)) : ℤ) : WithTop ℤ)
      norm_cast
      ring

include hq hcompat hcenter in
/-- Exact interface required by the unchanged original local-inertia source. -/
theorem restriction (e : ℕ) (he : addVal R (f q) = e)
    (x : RatFunc F) (hx : x ≠ 0) :
    value R L (algebraMap (RatFunc F) L x) = e • primePlace q hq x := by
  rw [rational_value q hq f hcompat hcenter e he x hx, primePlace_order q hq x hx]
  norm_cast
  all_goals simp only [nsmul_eq_mul]
end CenteredDVRRestriction318
