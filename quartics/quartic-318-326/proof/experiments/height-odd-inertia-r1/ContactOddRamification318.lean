module
public import RationalFourRootOddInertia318
public import ContactFieldRamification318
public section
noncomputable section
namespace ContactOddRamification318
open NumberField ContactRadical318 ContactIntegerRadicands318 ContactFieldRamification318
open scoped NumberField
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra

/-- At every odd rational prime, including the odd-contact primes and the
fixed primes 3 and 7, actual inertia in the original contact field has size
at most two. -/
theorem inertia_card_le_two (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0)
    (p : ℕ) [Fact p.Prime] (h2 : ¬(p : ℤ) ∣ 2)
    (P : Ideal (𝓞 (L u v))) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (P.inertia (G u v)) ≤ 2 :=
  RationalFourRootOddInertia318.inertia_card_le_two _ (v : ℚ)
    (by exact_mod_cast v_ne_zero u v hn) (radicand u v) (radicand_ne_zero u v hn)
    (scaled_parameter u v hn) p h2 P (P.over_def _).symm

/-- The same integer-ring extension has ramification index one or two at
every odd rational prime, proved through its actual inertia group. -/
theorem ramification_index_one_or_two (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0)
    (p : ℕ) [Fact p.Prime] (h2 : ¬(p : ℤ) ∣ 2)
    (P : Ideal (𝓞 (L u v))) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P.ramificationIdx ℤ = 1 ∨ P.ramificationIdx ℤ = 2 := by
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  let : q.IsPrime := Ideal.isPrime_of_liesOver P q
  let : IsGaloisGroup (G u v) ℚ (L u v) := inferInstance
  let : IsGaloisGroup (G u v) ℤ (𝓞 (L u v)) :=
    IsGaloisGroup.of_isFractionRing (G u v) ℤ (𝓞 (L u v)) ℚ (L u v)
  have hi := inertia_card_le_two u v hn p h2 P
  rw [Ideal.card_inertia_eq_ramificationIdxIn q P,
    Ideal.ramificationIdxIn_eq_ramificationIdx q P (G u v)] at hi
  have hp := P.ramificationIdx_pos ℤ
  omega

/-- In particular the actual ramification index is prime to the residue
characteristic at every odd rational prime. -/
theorem ramification_index_coprime (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0)
    (p : ℕ) [Fact p.Prime] (h2 : ¬(p : ℤ) ∣ 2)
    (P : Ideal (𝓞 (L u v))) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.Coprime p (P.ramificationIdx ℤ) := by
  rcases ramification_index_one_or_two u v hn p h2 P with h | h
  · rw [h]; exact Nat.coprime_one_right p
  · rw [h]
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    exact fun hp => h2 (by exact_mod_cast hp)

end ContactOddRamification318
