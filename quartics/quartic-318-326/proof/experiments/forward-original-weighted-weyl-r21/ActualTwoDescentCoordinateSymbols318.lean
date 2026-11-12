module
public import ActualTwoDescentTorsionComparison318
public section
noncomputable section
namespace ActualTwoDescentCoordinateSymbols318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentStrippedSymbols318
open ActualTwoDescentSignReciprocity318 ActualTwoDescentSymbolTable318
open ActualTwoDescentPrimeLaplacian318 ActualTwoDescentThreeSymbol318
open ActualTwoDescentSupportParity318 ActualTwoDescentTorsionComparison318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def firstRepresentative (p : ι → ℕ) (δ : ZMod 2) (u : ι → ZMod 2) : ℕ :=
  3^δ.val*monomial p u

def firstStripped (p : ι → ℕ) (δ : ZMod 2) (u : ι → ZMod 2) (i : ι) : ℕ :=
  3^δ.val*stripped p u i

lemma actual_first_factor (p : ι → ℕ) (δ : ZMod 2) (u : ι → ZMod 2) (i : ι) :
    firstRepresentative p δ u=(p i)^(u i).val*firstStripped p δ u i := by
  rw [firstRepresentative,firstStripped,actual_stripped_factor p u i]
  ring

lemma actual_first_valuation (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp3 : ∀ i, p i ≠ 3)
    (δ : ZMod 2) (u : ι → ZMod 2) (i : ι) :
    padicValNat (p i) (firstRepresentative p δ u)=(u i).val := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  rw [firstRepresentative,padicValNat.mul (pow_ne_zero _ (by decide : (3 : ℕ) ≠ 0))
    (monomial_pos p u).ne',padicValNat.pow,padicValNat_primes (hp3 i),mul_zero,
    zero_add,actual_monomial_valuation p hd]

/-- The first unit coordinate is the Jacobi symbol of the LITERAL
prime-free part of 3^delta times the squarefree representative. -/
theorem actual_first_stripped_symbol (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp3 : ∀ i, p i ≠ 3)
    (δ : ZMod 2) (u : ι → ZMod 2) (i : ι) :
    jacobiSym (firstStripped p δ u i : ℤ) (p i)=
      sign (δ*lambda p i+(edges p *ᵥ u) i) := by
  have hc : Nat.Coprime 3 (p i) :=
    (Nat.coprime_primes (by decide : Nat.Prime 3) Fact.out).mpr (Ne.symm (hp3 i))
  rw [firstStripped,Nat.cast_mul,Nat.cast_pow,jacobiSym.mul_left,jacobiSym.pow_left,
    actual_stripped_symbol p hd,sign_add,←actual_sign_symbol 3 (p i) hc]
  rw [show δ*lambda p i=lambda p i*δ from mul_comm _ _,sign_mul_bit]
  rfl

lemma actual_three_reverse_symbol (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    symbolBit p 3=symbolBit 3 p+((p/2 : ℕ) : ZMod 2) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h := actual_symbol_reciprocity p 3 hp2 (by decide) hp3
  norm_num only [show 3/2=(1 : ℕ) from rfl,Nat.cast_one,mul_one] at h
  linear_combination h

/-- The third finite equation is the exact actual quadratic-residue
condition at3 for the positive second-coordinate representative. -/
theorem actual_three_condition (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3) (v : ι → ZMod 2) :
    jacobiSym (monomial p v : ℤ) 3=1 ↔ dotProduct (lambda p+parity p) v=0 := by
  have hc : ∀ i ∈ (Finset.univ : Finset ι), Nat.Coprime (p i) 3 := by
    intro i _
    exact (Nat.coprime_primes Fact.out (by decide : Nat.Prime 3)).mpr (hp3 i)
  have he : jacobiSym (monomial p v : ℤ) 3=sign (dotProduct (lambda p+parity p) v) := by
    rw [monomial,actual_weighted_jacobi Finset.univ p v 3 hc]
    congr 1
    simp only [dotProduct,Pi.add_apply,lambda,parity,actual_three_reverse_symbol _ (hp2 _) (hp3 _)]
  rw [he,←sign_zero,sign_injective.eq_iff]

end ActualTwoDescentCoordinateSymbols318
