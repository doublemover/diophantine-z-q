module
public import LiteralPolynomialBasisEquiv318
public section
noncomputable section
namespace ActualSlicePolynomialPreparation318
open LiteralSliceModulus318 TernaryChartModuli318 LiteralSievePolynomial318
open LiteralPolynomialBasisEquiv318 LiteralSecondSievePolynomial318
set_option maxHeartbeats 2000000

/-- The actual rational polynomial substitution of an original slice
lattice, with the same finite/infinity moduli that define its integer basis. -/
@[expose] def substitution (κ t : ℤ)
    (s : ∀ i : PrimeIndex κ t, Option (ZMod (prime κ t i))) (A D : ℤ) : Poly →ₐ[ℚ] Poly :=
  forward (finiteModulus (prime κ t) s:ℚ) (infinityModulus (prime κ t) s:ℚ) A D

/-- Both actual original pairs remain rationally relatively prime after
the actual original lattice basis substitution. No new coprimality input. -/
theorem actual_pairs_relPrime (κ t : ℤ) (hκ : κ≠0) (ht : t≠0)
    (s : ∀ i : PrimeIndex κ t, Option (ZMod (prime κ t i))) (A D : ℤ) :
    IsRelPrime (substitution κ t s A D (firstP κ t))
      (substitution κ t s A D (productD t)) ∧
    IsRelPrime (substitution κ t s A D (secondP κ t))
      (substitution κ t s A D (normK κ t)) := by
  obtain ⟨hq,hr⟩ := moduli_positive (prime κ t) (prime_is_prime κ t) s
  have hq' : (finiteModulus (prime κ t) s:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hq
  have hr' : (infinityModulus (prime κ t) s:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hr
  have hk' : (κ:ℚ)≠0 := by exact_mod_cast hκ
  have ht' : (t:ℚ)≠0 := by exact_mod_cast ht
  constructor
  · exact preserves_relPrime _ _ _ _ hq' hr' _ _ (first_pair_relPrime κ t ht')
  · exact preserves_relPrime _ _ _ _ hq' hr' _ _ (second_pair_relPrime κ t hk' ht')

/-- The K-D identity also excludes common content for the first chart's
ACTUAL replacement pair(P,D), not only for the unreplaced pair(P,K). -/
lemma replacement_pair_nonzero (p : ℕ) (κ t : ℤ)
    (v : TernaryQuadraticLineCover318.Vector ℤ)
    (hK : ¬(p:ℤ)∣LiteralAdjacentNormSlice318.K κ t v) :
    ¬((p:ℤ)∣LiteralAdjacentNormSlice318.P κ t v ∧
      (p:ℤ)∣LiteralAdjacentNormSlice318.D t v) := by
  rintro ⟨hP,hD⟩
  apply hK
  have he : LiteralAdjacentNormSlice318.K κ t v=
      LiteralAdjacentNormSlice318.D t v+LiteralAdjacentNormSlice318.P κ t v*
        (LiteralAdjacentNormSlice318.P κ t v+2*t^2-2*v.1*v.2.1) := by
    linear_combination LiteralAdjacentNormSlice318.K_difference κ t v
  rw [he]
  exact dvd_add hD (dvd_mul_of_dvd_left hP _)

/-- Actual integer evaluation witnesses for BOTH selected sieve pairs,
after the exact original lattice substitution. -/
theorem actual_pair_nonzero_value (p : ℕ) [Fact p.Prime] (κ t : ℤ)
    (ht : ¬(p:ℤ)∣t)
    (s : ∀ i : PrimeIndex κ t, Option (ZMod (prime κ t i))) (A D : ℤ) :
    ∃ u : TernaryQuadraticLineCover318.Vector ℤ,
      let v := TriangularTernaryBasis318.basisMap (finiteModulus (prime κ t) s:ℤ)
        (infinityModulus (prime κ t) s:ℤ) A D u
      (¬((p:ℤ)∣LiteralAdjacentNormSlice318.P κ t v ∧
        (p:ℤ)∣LiteralAdjacentNormSlice318.D t v)) ∧
      (¬((p:ℤ)∣LiteralAdjacentNormSlice318.P' κ t v ∧
        (p:ℤ)∣LiteralAdjacentNormSlice318.K κ t v)) := by
  obtain ⟨u,hu⟩ := LiteralBasisContent318.actual_basis_nonzero_value p κ t ht s A D
  exact ⟨u,replacement_pair_nonzero p κ t _ hu,fun hh => hu hh.2⟩

/-- Full algebraic preparation at the original slice: rational coprimality
and explicit integer evaluations excluding new common content primes. The
quantitative geometric-sieve theorem remains separate. -/
theorem actual_sieve_polynomial_preparation (κ t : ℤ) (hκ : κ≠0) (ht : t≠0)
    (s : ∀ i : PrimeIndex κ t, Option (ZMod (prime κ t i))) (A D : ℤ) :
    (IsRelPrime (substitution κ t s A D (firstP κ t))
      (substitution κ t s A D (productD t)) ∧
     IsRelPrime (substitution κ t s A D (secondP κ t))
      (substitution κ t s A D (normK κ t))) ∧
    (∀ (p : ℕ) (hp : p.Prime), ¬(p:ℤ)∣t →
      ∃ u : TernaryQuadraticLineCover318.Vector ℤ,
        ¬(p:ℤ)∣LiteralAdjacentNormSlice318.K κ t
          (TriangularTernaryBasis318.basisMap (finiteModulus (prime κ t) s:ℤ)
            (infinityModulus (prime κ t) s:ℤ) A D u)) := by
  refine ⟨actual_pairs_relPrime κ t hκ ht s A D,?_⟩
  intro p hp hpt
  letI : Fact p.Prime := ⟨hp⟩
  exact LiteralBasisContent318.actual_basis_nonzero_value p κ t hpt s A D

end ActualSlicePolynomialPreparation318
