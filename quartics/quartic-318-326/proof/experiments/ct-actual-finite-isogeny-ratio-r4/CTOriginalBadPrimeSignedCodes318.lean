module
public import CTOriginalRationalSquarefree318
public import ActualTwoDescentSquareClassQuotient318
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.SetTheory.Cardinal.Finite
public section
noncomputable section

namespace ActualNaturalAllPlacesFinite318

open ActualTwoDescentPrimeMonomials318 ActualTwoDescentRationalSquarefree318 ActualTwoDescentSquareClassQuotient318

abbrev Support (n : ℕ) := {p : ℕ // p ∈ (6*n).primeFactors}
abbrev Code (n : ℕ) := ZMod 2 × (Support n → ZMod 2)

private abbrev primeAt (n : ℕ) (i : Support n) : ℕ := i.val

/-- A finite code for squareclasses with support in 6n, including the sign.
Surjectivity onto the actual all-place set is not assumed for the code map:
only that every actual class is represented somewhere in its finite range. -/
def supportedClass (n : ℕ) (a : Code n) : SquareClass ℚ := by
  letI : ∀ i : Support n, Fact (primeAt n i).Prime :=
    fun i => ⟨Nat.prime_of_mem_primeFactors i.property⟩
  exact classOf ((-1 : ℚ)^a.1.val * (monomial (primeAt n) a.2 : ℚ))
    (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (monomial_pos (primeAt n) a.2).ne'))

private theorem outside (n : ℕ) (hn : n≠0) (q : ℕ) (hq : q.Prime)
    (hout : ∀ i : Support n, q ≠ primeAt n i) :
    q≠2 ∧ q≠3 ∧ ¬q∣n := by
  have hbad : ¬ q ∣ 6*n := by
    intro hd
    exact hout ⟨q,Nat.mem_primeFactors.mpr ⟨hq,hd,mul_ne_zero (by decide) hn⟩⟩ rfl
  refine ⟨?_,?_,?_⟩
  · rintro rfl
    exact hbad (dvd_mul_of_dvd_left (by decide : 2 ∣ 6) n)
  · rintro rfl
    exact hbad (dvd_mul_of_dvd_left (by decide : 3 ∣ 6) n)
  · intro hd
    exact hbad (dvd_mul_of_dvd_right hd 6)

/-- Outside the literal support of 6n precisely the three good-prime
exclusions needed by the local cubic proof hold (for n nonzero). -/
theorem outside_bad_prime_support (n : ℕ) (hn : n≠0) (q : ℕ) (hq : q.Prime)
    (hout : q ∉ (6*n).primeFactors) : q≠2 ∧ q≠3 ∧ ¬q∣n := by
  apply outside n hn q hq
  intro i he
  apply hout
  change q=i.val at he
  rw [he]
  exact i.property

/-- Signed support of an actual rational squareclass: the finite code is
literal, and this direction does not assert local solubility of any code. -/
theorem supported_class_of_outside_valuations (n : ℕ) (A : ℚ) (hA : A≠0)
    (hpar : ∀ q : ℕ, q.Prime → q ∉ (6*n).primeFactors → Even (padicValRat q A)) :
    ∃ a : Code n, supportedClass n a = classOf A hA := by
  letI : ∀ i : Support n, Fact (primeAt n i).Prime :=
    fun i => ⟨Nat.prime_of_mem_primeFactors i.property⟩
  have hi : Function.Injective (primeAt n) := fun _ _ h => Subtype.ext h
  obtain ⟨e,u,r,hr,he⟩ := actual_signed_supported_rational (primeAt n) hi A hA
    (fun q hq ho => hpar q hq (fun h => ho ⟨q,h⟩ rfl))
  refine ⟨(e,u),?_⟩
  unfold supportedClass
  exact ((class_of_eq_iff _ _ _ _).mpr ⟨r,hr,he⟩).symm

theorem finite_signed_code_range (n : ℕ) :
    Finite (Set.range (supportedClass n)) := by
  classical
  let intoRange : Code n → Set.range (supportedClass n) :=
    fun a => ⟨supportedClass n a,⟨a,rfl⟩⟩
  exact Finite.of_surjective intoRange (by
    rintro ⟨_,a,rfl⟩
    exact ⟨a,rfl⟩)

end ActualNaturalAllPlacesFinite318
