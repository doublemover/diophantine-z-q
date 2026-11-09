module
public import ContactFieldRamification318
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Smooth.Fiber
public section
noncomputable section
namespace ContactIntegerEtaleLocus318
open NumberField ContactRadical318 ContactFieldRamification318
open scoped NumberField
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra

local instance (u v : ℤ) : Algebra.FinitePresentation ℤ (𝓞 (L u v)) :=
  Algebra.FinitePresentation.of_finiteType.mp inferInstance

/-- The original fixed bad-prime product times the original literal
odd-contact radical; no smaller exceptional set is substituted. -/
@[expose] def excludedProduct (u v : ℤ) : ℕ := badProduct * radical u v

lemma excludedProduct_pos (u v : ℤ) : 0 < excludedProduct u v := by
  rw [excludedProduct, bad_product_exact]
  exact Nat.mul_pos (by norm_num) (radical_pos u v)

lemma bad_dvd_excludedProduct (u v : ℤ) (p : ℕ) (hp : p ∈ badPrimes) :
    p ∣ excludedProduct u v := by
  exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp) _

lemma contact_dvd_excludedProduct (u v : ℤ) (p : ℕ) (hp : p ∈ contactPrimes u v) :
    p ∣ excludedProduct u v := by
  exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun q : ℕ => q) hp) _

/-- The actual integer-ring extension is etale at every prime of the
original ring of integers at which the original excluded product is a unit.
The generic prime is included explicitly. -/
theorem etale_at (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0)
    (P : Ideal (𝓞 (L u v))) [P.IsPrime]
    (hN : (excludedProduct u v : 𝓞 (L u v)) ∉ P) : Algebra.IsEtaleAt ℤ P := by
  have hu : Algebra.IsUnramifiedAt ℤ P := by
    by_cases hP : P = ⊥
    · subst P
      exact Algebra.isUnramifiedAt_bot
    · let : NeZero P := ⟨hP⟩
      let p := Ideal.absNorm (P.under ℤ)
      let : Fact p.Prime := ⟨Nat.absNorm_under_prime P⟩
      have hnd : ¬p ∣ excludedProduct u v := by
        intro hd
        apply hN
        have hdi : (p : ℤ) ∣ (excludedProduct u v : ℤ) := by exact_mod_cast hd
        simpa only [Int.cast_natCast] using (Int.cast_mem_ideal_iff (I := P)).mpr hdi
      exact ContactFieldRamification318.unramified_at u v hn p
        (fun hp => hnd (bad_dvd_excludedProduct u v p hp))
        (fun hp => hnd (contact_dvd_excludedProduct u v p hp)) P
  let := hu
  exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat P

/-- The actual principal open obtained by inverting precisely the original
excluded product lies in the actual etale locus of the integer ring. -/
theorem basicOpen_subset_etaleLocus (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0) :
    (PrimeSpectrum.basicOpen (excludedProduct u v : 𝓞 (L u v)) : Set (PrimeSpectrum (𝓞 (L u v)))) ⊆
      Algebra.etaleLocus ℤ (𝓞 (L u v)) := by
  intro P hP
  exact etale_at u v hn P.asIdeal hP

/-- An actual localization of the same ring of integers is etale over Z.
This is not a postulated etale model or a change of its fraction field. -/
theorem integerLocalization_etale (u v : ℤ) (hn : ∀ j, forms u v j ≠ 0) :
    Algebra.Etale ℤ (Localization.Away (excludedProduct u v : 𝓞 (L u v))) :=
  Algebra.basicOpen_subset_etaleLocus_iff_etale.mp (basicOpen_subset_etaleLocus u v hn)

end ContactIntegerEtaleLocus318
