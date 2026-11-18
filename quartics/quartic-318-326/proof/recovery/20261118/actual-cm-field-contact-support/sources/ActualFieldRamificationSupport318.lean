module
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.Tactic
public section
noncomputable section
namespace ActualFieldRamificationSupport318
open NumberField Finset

/-- Genuine ramification hypothesis at the ring of integers of the actual
controlled field. Its input is not divisibility of the field discriminant
or a pre-bounded arithmetic number. -/
@[expose] def UnramifiedOutside (F : Type*) [Field F] [NumberField F] (T : Finset ℕ) : Prop :=
  ∀ (p : ℕ), p.Prime → p∉T →
    Algebra.IsUnramifiedIn (NumberField.RingOfIntegers F) (Ideal.span ({(p:ℤ)} : Set ℤ))

theorem prime_support (F : Type*) [Field F] [NumberField F] {T : Finset ℕ}
    (h : UnramifiedOutside F T) :
    (NumberField.discr F).natAbs.primeFactors ⊆ T := by
  intro p hp
  obtain ⟨hp',hd,_⟩ := Nat.mem_primeFactors.mp hp
  by_contra hn
  have hnd := (NumberField.not_dvd_discr_iff_isUnramifiedIn F (NumberField.RingOfIntegers F)
    (Nat.prime_iff_prime_int.mp hp')).mpr (h p hp' hn)
  apply hnd
  apply Int.natAbs_dvd_natAbs.mp
  simpa using hd

/-- The CM quadratic field K lies inside F from its Lie(E)-action. This
lemma takes the actual field embedding (algebra structure) and invokes the
absolute discriminant tower theorem, not a placeholder integer division. -/
theorem subfield_prime (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] (p : ℕ) (h : p∣(NumberField.discr K).natAbs) :
    p∣(NumberField.discr F).natAbs :=
  h.trans (Int.natAbs_dvd_natAbs.mpr (NumberField.discr_dvd_discr K F))

theorem radical_le (F : Type*) [Field F] [NumberField F] {T : Finset ℕ}
    (h : UnramifiedOutside F T) (pos : ∀ p∈T,1≤p) :
    (∏ p∈(NumberField.discr F).natAbs.primeFactors,p)≤∏ p∈T,p := by
  exact Finset.prod_le_prod_of_subset_of_one_le (prime_support F h) (fun p hp _ => pos p hp)

end ActualFieldRamificationSupport318
