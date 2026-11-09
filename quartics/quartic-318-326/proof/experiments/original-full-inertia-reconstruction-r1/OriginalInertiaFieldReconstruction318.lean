module
public import QuadraticLocalCharacterOrders318
public import ContactPrimeOrderParity318
public section
noncomputable section
open scoped BigOperators
namespace OriginalInertiaFieldReconstruction318
open Polynomial IsLocalRing GaloisCharacterContactReconstruction318
open RationalFunctionEvenSquare318 PolynomialPrimeValuation318 DVRFractionCharacterParity318
universe u

@[expose] def expectedBit (q : ℚ[X]) (i : Fin 4) : Bool := by
  classical
  exact decide (q ∣ SourceTwistArithmetic318.cubic i)

lemma expectedBit_false (q : ℚ[X]) (i : Fin 4) :
    expectedBit q i = false ↔ ¬ q ∣ SourceTwistArithmetic318.cubic i := by
  classical
  simp [expectedBit]

variable {L : Type u} [Field L] [Algebra (RatFunc ℚ) L]
  [FiniteDimensional (RatFunc ℚ) L] [IsGalois (RatFunc ℚ) L]

/-- Genuine local data on the ORIGINAL field, not a parity or reconstruction
assertion. Each finite prime has an actual DVR with that exact fraction field.
The ramified case retains the original Galois element, its local restriction,
its action on the FULL residue field, an actual negated uniformizer, index2
valuation restriction and its specified four character signs. -/
structure LocalModel (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (q : ℚ[X]) (hq : Prime q) where
  Ring : Type u
  [ring : CommRing Ring]
  [domain : IsDomain Ring]
  [dvr : IsDiscreteValuationRing Ring]
  [algebra : Algebra Ring L]
  [fraction : IsFractionRing Ring L]
  [residueCharZero : CharZero (ResidueField Ring)]
  local_cases :
    ((∀ a : RatFunc ℚ, a ≠ 0 →
        value Ring L (algebraMap (RatFunc ℚ) L a) = primePlace q hq a) ∧
      ∀ i, ¬ q ∣ SourceTwistArithmetic318.cubic i) ∨
    ∃ (σ : L ≃ₐ[RatFunc ℚ] L) (τ : Ring ≃+* Ring) (π : Ring),
      (∀ a : RatFunc ℚ, a ≠ 0 →
        value Ring L (algebraMap (RatFunc ℚ) L a) = 2 • primePlace q hq a) ∧
      (∀ x : Ring, σ (algebraMap Ring L x) = algebraMap Ring L (τ x)) ∧
      (∀ x : Ring, residue Ring (τ x) = residue Ring x) ∧
      Irreducible π ∧ τ π = -π ∧
      ∀ i, character labels i σ = if expectedBit q i then -1 else 1

attribute [instance] LocalModel.ring LocalModel.domain LocalModel.dvr LocalModel.algebra
  LocalModel.fraction LocalModel.residueCharZero

/-- The local data derive, rather than assume, parity of the original actual
normal-basis character functions. The inverse case handles every pole. -/
theorem original_orders
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (models : ∀ (q : ℚ[X]) (hq : Prime q), LocalModel labels q hq)
    (i : Fin 4) (q : ℚ[X]) (hq : Prime q) :
    Even (orderAt q (radicand labels i)) ↔ ¬ q ∣ SourceTwistArithmetic318.cubic i := by
  let d := models q hq
  rcases d.local_cases with hu | ⟨σ, τ, π, hr, hc, hres, hπ, hτπ, hs⟩
  · have he := QuadraticLocalCharacterOrders318.unramified (R := d.Ring) q hq hu.1
      (radicand labels i) (radicand_ne_zero labels i) (root labels i) (root_square labels i)
    exact iff_of_true he (hu.2 i)
  · have hroot : σ (root labels i) =
        (if expectedBit q i then -1 else 1) * root labels i := by
      rw [root_action, hs, Algebra.smul_def]
      cases expectedBit q i <;> simp
    have he := QuadraticLocalCharacterOrders318.ramified (R := d.Ring) q hq hr τ
      σ.toRingEquiv hc hres π hπ hτπ (radicand labels i) (radicand_ne_zero labels i)
      (root labels i) (root_square labels i) (expectedBit q i) hroot
    exact he.trans (expectedBit_false q i)

/-- End-to-end algebraic/local reconstruction from original labeled finite
Galois data and ACTUAL per-prime local DVR/inertia models. Neither radicals,
degree16, squareclasses, nor parity of the original functions are supplied.
Constructing these local models from the PEL curve remains geometric work. -/
theorem reconstruct
    (labels : (L ≃ₐ[RatFunc ℚ] L) ≃* FourBinaryCharacters318.Group)
    (models : ∀ (q : ℚ[X]) (hq : Prime q), LocalModel labels q hq) :
    ∃ c : Fin 4 → ℚˣ,
      ∃ e : KummerTensorField318.Raw (SourceKummerField318.parameter c) ≃ₐ[RatFunc ℚ] L,
        ∀ (σ : L ≃ₐ[RatFunc ℚ] L) z, σ (e z) = e
          (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c)
            (FourBinaryCharacters318.signPattern (labels σ)) z) :=
  ContactPrimeOrderParity318.reconstruct_from_local_orders labels (original_orders labels models)
end OriginalInertiaFieldReconstruction318
