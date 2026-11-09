module
public import RationalFourRootInertia318
public import ContactIntegerRadicands318
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RingTheory.Ideal.Int
public section
noncomputable section
namespace ContactFieldRamification318
open NumberField ContactRadical318 ContactIntegerRadicands318
open scoped NumberField
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev L (u v : ℤ) := RationalContactPoint318.PointField SourceTwistArithmetic318.units
  (32 * ((u : ℚ) / (v : ℚ)))
abbrev G (u v : ℤ) := L u v ≃ₐ[ℚ] L u v

/-- Actual ideal-theoretic inertia in the same constructed number field is
trivial at every good prime outside the literal odd-contact support. -/
theorem inertia_eq_bot (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0)
    (p : ℕ) [Fact p.Prime] (hg : p ∉ badPrimes) (ho : p ∉ contactPrimes u v)
    (P : Ideal (𝓞 (L u v))) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.inertia (G u v) = ⊥ := by
  have h2 : ¬(p : ℤ) ∣ 2 := by
    exact_mod_cast ContactPrimeLimits318.good_not_dvd p 2 Fact.out hg (by simp [badPrimes])
  exact RationalFourRootInertia318.inertia_eq_bot _ (v : ℚ)
    (by exact_mod_cast v_ne_zero u v hn) (radicand u v) (radicand_ne_zero u v hn)
    (scaled_parameter u v hn) p h2 (radicand_valuation_even u v hn p hg ho)
    P (P.over_def _).symm

/-- The actual ramification index of every prime above such a rational
prime is one, derived from the original field's actual inertia group. -/
theorem ramification_index_one (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0)
    (p : ℕ) [Fact p.Prime] (hg : p ∉ badPrimes) (ho : p ∉ contactPrimes u v)
    (P : Ideal (𝓞 (L u v))) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.ramificationIdx ℤ = 1 := by
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  let : q.IsPrime := Ideal.isPrime_of_liesOver P q
  let : IsGaloisGroup (G u v) ℚ (L u v) := inferInstance
  let : IsGaloisGroup (G u v) ℤ (𝓞 (L u v)) :=
    IsGaloisGroup.of_isFractionRing (G u v) ℤ (𝓞 (L u v)) ℚ (L u v)
  have hi : Nat.card (P.inertia (G u v)) = 1 := by
    rw [inertia_eq_bot u v hn p hg ho P]
    simp
  rw [Ideal.card_inertia_eq_ramificationIdxIn q P,
    Ideal.ramificationIdxIn_eq_ramificationIdx q P (G u v)] at hi
  exact hi

/-- The same original ring-of-integers extension is unramified at every
prime outside the fixed bad set and the actual odd-contact support. -/
theorem unramified_at (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0)
    (p : ℕ) [Fact p.Prime] (hg : p ∉ badPrimes) (ho : p ∉ contactPrimes u v)
    (P : Ideal (𝓞 (L u v))) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Algebra.IsUnramifiedAt ℤ P := by
  let : Algebra.HasSeparableResidueFieldsAt ℤ (𝓞 (L u v)) (P.under ℤ) := by
    simpa only [P.over_def (Ideal.span {(p : ℤ)})] using
      (inferInstance : Algebra.HasSeparableResidueFieldsAt ℤ (𝓞 (L u v))
        (Ideal.span {(p : ℤ)}))
  exact Ideal.ramificationIdx_eq_one_iff.mp (ramification_index_one u v hn p hg ho P)

/-- All possible ramified rational primes lie in the fixed bad set or the
literal odd-contact support appearing in the intended height bound. -/
theorem ramified_prime_support (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0)
    (p : ℕ) [Fact p.Prime]
    (P : Ideal (𝓞 (L u v))) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hram : P.ramificationIdx ℤ ≠ 1) : p ∈ badPrimes ∨ p ∈ contactPrimes u v := by
  by_contra h
  exact hram (ramification_index_one u v hn p (not_or.mp h).1 (not_or.mp h).2 P)

end ContactFieldRamification318
