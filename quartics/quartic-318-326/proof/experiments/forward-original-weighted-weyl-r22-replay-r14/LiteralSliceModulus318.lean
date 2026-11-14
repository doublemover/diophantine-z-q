module
public import LiteralQuarticSlice318
public import Mathlib.Data.Nat.PrimeFin
public section
noncomputable section
namespace LiteralSliceModulus318
set_option maxHeartbeats 1000000

/-- Exactly the manuscript's retained primes of the actual slice label:
prime divisors of |t| outside the original coefficient2κ. -/
@[expose] def retained (κ t : ℤ) : Finset ℕ :=
  t.natAbs.primeFactors.filter (fun p => ¬(p:ℤ)∣2*κ)
@[expose] def PrimeIndex (κ t : ℤ) := ↥(retained κ t)
@[expose] def prime (κ t : ℤ) (i : PrimeIndex κ t) : ℕ := i.1

lemma prime_is_prime (κ t : ℤ) (i : PrimeIndex κ t) : (prime κ t i).Prime :=
  Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp i.2).1
lemma prime_injective (κ t : ℤ) : Function.Injective (prime κ t) := Subtype.val_injective
lemma prime_avoids (κ t : ℤ) (i : PrimeIndex κ t) : ¬(prime κ t i:ℤ)∣2*κ :=
  (Finset.mem_filter.mp i.2).2
lemma prime_odd (κ t : ℤ) (i : PrimeIndex κ t) : prime κ t i≠2 := by
  intro he
  apply prime_avoids κ t i
  rw [he]
  exact dvd_mul_right 2 κ
lemma prime_avoids_coefficient (κ t : ℤ) (i : PrimeIndex κ t) : ¬(prime κ t i:ℤ)∣κ := by
  intro hd
  exact prime_avoids κ t i (dvd_mul_of_dvd_right hd 2)
lemma prime_divides_label (κ t : ℤ) (i : PrimeIndex κ t) : (prime κ t i:ℤ)∣t := by
  apply Int.dvd_natAbs.mp
  exact Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp i.2).1)

@[expose] def modulus (κ t : ℤ) : ℕ := FixedSquarefreeCRT318.modulus (prime κ t)
lemma modulus_positive (κ t : ℤ) : 0<modulus κ t :=
  FixedSquarefreeCRT318.modulus_positive (prime κ t) (prime_is_prime κ t)

/-- Constructed from the literal slice, not an input modulus/CRT family. -/
theorem modulus_divides_label (κ t : ℤ) : (modulus κ t:ℤ)∣t := by
  apply (SquarefreeTernaryLatticeCover318.product_divisor_iff
    (prime κ t) (prime_is_prime κ t) (prime_injective κ t) t).mpr
  exact prime_divides_label κ t

theorem modulus_le_label (κ t : ℤ) (ht : t≠0) : modulus κ t≤t.natAbs := by
  apply Nat.le_of_dvd (Int.natAbs_pos.mpr ht)
  simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr (modulus_divides_label κ t)

/-- Every actual original slice point is in one of the constructed original
integer lattices, with the correct literal coefficient and original modulus. -/
theorem actual_slice_cover (κ t : ℤ) (side : Bool) (v : LiteralQuarticSlice318.Slice κ t side) :
    ∃ s : ∀ i : PrimeIndex κ t, Option (ZMod (prime κ t i)),
      LiteralQuarticSlice318.project v.1.1∈
        LiteralTernaryReduction318.literalLattice (prime κ t) κ s := by
  apply (LiteralTernaryReduction318.literal_kernel_cover
    (prime κ t) (prime_is_prime κ t) (prime_injective κ t) (prime_odd κ t)
    κ (prime_avoids_coefficient κ t) _).mp
  exact LiteralQuarticSlice318.slice_modulus_divides κ t side v
    (modulus κ t) (modulus_divides_label κ t)

/-- Index of every actual literal slice lattice. No supplied prime family,
modulus or coordinate scaling occurs in this consumer. -/
theorem actual_lattice_index (κ t : ℤ)
    (s : ∀ i : PrimeIndex κ t, Option (ZMod (prime κ t i))) :
    (LiteralTernaryReduction318.literalLattice (prime κ t) κ s).index=(modulus κ t)^2 :=
  LiteralTernaryReduction318.literal_lattice_index
    (prime κ t) (prime_is_prime κ t) (prime_injective κ t) (prime_odd κ t) κ s

end LiteralSliceModulus318
