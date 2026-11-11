module
public import ActualTwoDescentFamilyProducts318
public section
noncomputable section
namespace ActualTwoDescentFamilyReciprocity318
open ActualTwoDescentPrimeFamily318 ActualTwoDescentResidueBits318
set_option maxHeartbeats 16000000

/-- Every reverse entry of the produced prime family is determined by the
actual quadratic reciprocity parity. Arbitrary symbols were prescribed in
only one direction, so this does not impose inconsistent square matrices. -/
theorem actual_family_reverse {ι : Type*} (p : ι → ℕ)
    (oldBits : ℕ → ι → Bool) (newBits : ℕ → ℕ → Bool)
    (special : ℕ → Bool) (forbidden : Finset ℕ) (N k : ℕ)
    (F : PrimeFamily p oldBits newBits special forbidden N k)
    (i j : Fin k) (hji : j.val < i.val) :
    jacobiSym (F.value j : ℤ) (F.value i)=
      (-1 : ℤ)^(F.value j/2*(F.value i/2))*bitSign (newBits i.val j.val) := by
  letI : Fact (F.value i).Prime := ⟨F.prime i⟩
  letI : Fact (F.value j).Prime := ⟨F.prime j⟩
  have hi : F.value i ≠ 2 := ne_of_gt (lt_of_le_of_lt (le_max_right _ _) (F.large i))
  have hj : F.value j ≠ 2 := ne_of_gt (lt_of_le_of_lt (le_max_right _ _) (F.large j))
  rw [←legendreSym.to_jacobiSym,legendreSym.quadratic_reciprocity' hj hi,
    legendreSym.to_jacobiSym,F.earlier_symbol i j hji]

/-- Reverse symbols against the fixed original beta/theta support are
also retained at the same actual primes. -/
theorem actual_seed_reverse {ι : Type*} (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hp2 : ∀ i, p i ≠ 2)
    (oldBits : ℕ → ι → Bool) (newBits : ℕ → ℕ → Bool)
    (special : ℕ → Bool) (forbidden : Finset ℕ) (N k : ℕ)
    (F : PrimeFamily p oldBits newBits special forbidden N k) (i : Fin k) (j : ι) :
    jacobiSym (p j : ℤ) (F.value i)=
      (-1 : ℤ)^(p j/2*(F.value i/2))*bitSign (oldBits i.val j) := by
  letI : Fact (F.value i).Prime := ⟨F.prime i⟩
  have hi : F.value i ≠ 2 := ne_of_gt (lt_of_le_of_lt (le_max_right _ _) (F.large i))
  rw [←legendreSym.to_jacobiSym,legendreSym.quadratic_reciprocity' (hp2 j) hi,
    legendreSym.to_jacobiSym,F.old_symbol i j]

end ActualTwoDescentFamilyReciprocity318
