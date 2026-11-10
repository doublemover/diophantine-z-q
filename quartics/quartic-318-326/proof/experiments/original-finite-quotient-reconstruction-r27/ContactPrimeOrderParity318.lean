module
public import PolynomialPrimeValuation318
public import GaloisCharacterContactReconstruction318
public section
noncomputable section
open scoped BigOperators
namespace ContactPrimeOrderParity318
attribute [local instance] Classical.propDecidable
open Polynomial SourceTwistArithmetic318 RationalFunctionEvenSquare318
open ContactDivisorFieldReconstruction318 PolynomialPrimeValuation318

lemma contact_polynomial (i : Fin 4) :
    contactProduct i = algebraMap ℚ[X] (RatFunc ℚ) (cubic i) := by
  simp only [contactProduct, ComplementSquareclass318.complementaryProduct,
    SourceKummerField318.parameter, Units.val_one, map_one, one_mul, cubic, map_prod]

lemma cubic_nonzero (i : Fin 4) : cubic i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact (monic_X_sub_C _).ne_zero

lemma cubic_squarefree (i : Fin 4) : Squarefree (cubic i) := by
  have hc : Function.Injective (complement i) := by fin_cases i <;> decide
  exact LinearContactSquareclass318.product_squarefree
    (fun j : Fin 3 => LinearContactSquareclass318.contacts (complement i j))
    (LinearContactSquareclass318.contacts_injective.comp hc) Finset.univ

/-- All irreducible polynomials are included. A complementary contact product
has order1 precisely at one of its three actual linear factors, and0 elsewhere. -/
theorem order_contact (q : ℚ[X]) (hq : Prime q) (i : Fin 4) :
    orderAt q (contactProduct i) = if q ∣ cubic i then 1 else 0 := by
  classical
  have hf := FiniteMultiplicity.of_prime_left hq (cubic_nonzero i)
  have hle := ((squarefree_iff_emultiplicity_le_one (cubic i)).mp (cubic_squarefree i) q).resolve_right
    hq.not_isUnit
  rw [hf.emultiplicity_eq_multiplicity] at hle
  have hbound : multiplicity q (cubic i) ≤ 1 := by exact_mod_cast hle
  have hv : primePlace q hq (contactProduct i) = (multiplicity q (cubic i) : ℤ) := by
    rw [contact_polynomial, primePlace_multiplicity q hq _ (cubic_nonzero i)]
  have ho : orderAt q (contactProduct i) = (multiplicity q (cubic i) : ℤ) := by
    have hh := (primePlace_order q hq _ (contactProduct_ne_zero i)).symm.trans hv
    exact_mod_cast hh
  rw [ho]
  by_cases hd : q ∣ cubic i
  · have hp := multiplicity_pos_of_dvd hd hf
    have hm : multiplicity q (cubic i) = 1 := by omega
    simp only [hd, if_pos, hm, Nat.cast_one]
  · rw [multiplicity_eq_zero_of_not_dvd hd]
    simp [hd]

lemma contact_even (q : ℚ[X]) (hq : Prime q) (i : Fin 4) :
    Even (orderAt q (contactProduct i)) ↔ ¬ q ∣ cubic i := by
  rw [order_contact q hq i]
  by_cases h : q ∣ cubic i <;> simp [h]

lemma order_div (q : ℚ[X]) (hq : Prime q) (x y : RatFunc ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    orderAt q (x / y) = orderAt q x - orderAt q y := by
  have hh : (orderAt q (x / y) : WithTop ℤ) =
      ((orderAt q x - orderAt q y : ℤ) : WithTop ℤ) := by
    rw [← primePlace_order q hq (x / y) (div_ne_zero hx hy), (primePlace q hq).map_div,
      primePlace_order q hq x hx, primePlace_order q hq y hy]
    norm_cast
  exact_mod_cast hh

/-- Actual local inertia parity, once supplied by the DVR calculation, gives
exactly the global squareclass input. No prime outside the known rational
contacts is dropped from the quantifier. -/
theorem ratio_even (q : ℚ[X]) (hq : Prime q) (i : Fin 4)
    (a : RatFunc ℚ) (ha : a ≠ 0) (horder : Even (orderAt q a) ↔ ¬ q ∣ cubic i) :
    Even (orderAt q (a / contactProduct i)) := by
  rw [order_div q hq a _ ha (contactProduct_ne_zero i), Int.even_sub]
  exact horder.trans (contact_even q hq i).symm

variable {L : Type*} [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]

/-- The full original-action-preserving reconstruction now consumes local
inertia-order conclusions. Genuine PEL local models and their restriction
identities are still required to instantiate those conclusions. -/
theorem reconstruct_from_local_orders
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (horders : ∀ i (q : ℚ[X]), Prime q →
      (Even (orderAt q (GaloisCharacterContactReconstruction318.radicand labels i)) ↔
        ¬ q ∣ cubic i)) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : KummerTensorField318.Raw (SourceKummerField318.parameter c) ≃ₐ[RatFunc ℚ] L,
        ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
          (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
            (FourBinaryCharacters318.signPattern (labels σ)) z) := by
  apply GaloisCharacterContactReconstruction318.reconstruct_equivariant labels
  intro i q hq
  exact ratio_even q hq i _ (GaloisCharacterContactReconstruction318.radicand_ne_zero labels i)
    (horders i q hq)
end ContactPrimeOrderParity318
