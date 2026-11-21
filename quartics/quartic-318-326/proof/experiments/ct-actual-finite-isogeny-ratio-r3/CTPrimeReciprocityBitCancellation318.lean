module
public import CTExplicitPrimeReciprocitySeeds318
public import CTNativeOddSquareclassCoordinates318
public import CTNativeDyadicSquareclassCoordinates318
import all CTNativeOddSquareclassCoordinates318
import Mathlib.Tactic.NormNum
import all Mathlib.NumberTheory.LegendreSymbol.Basic
import all CTNativeDyadicSquareclassCoordinates318
public section
noncomputable section

namespace CTPrimeReciprocityBitCancellation318

open CTNativePadicValuationBit318 CTNativeOddSquareclassCoordinates318
open CTNativeDyadicSquareclassCoordinates318 CTExplicitPrimeReciprocitySeeds318
open ZMod

private theorem signBit_mul_checked (x y : ℤ)
    (hx : x=1 ∨ x= -1) (hy : y=1 ∨ y= -1) :
    signBit (x*y)=signBit x+signBit y := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> decide

private theorem negOnePow_pm (j : ℕ) : (-1:ℤ)^j=1 ∨ (-1:ℤ)^j= -1 := by
  induction j with
  | zero => exact Or.inl (pow_zero _)
  | succ j h =>
    rw [pow_succ]
    rcases h with h|h <;> rw [h] <;> decide

private theorem negOnePow_bit (j : ℕ) : signBit ((-1:ℤ)^j)=(j:Bit) := by
  induction j with
  | zero => decide
  | succ j h =>
    rw [pow_succ,signBit_mul_checked _ _ (negOnePow_pm j) (Or.inr rfl),
      h,show signBit (-1:ℤ)=1 from rfl,Nat.cast_succ]

/-- Literal residue rows, not a new abstract Hilbert symbol.
The calculation is exactly the four odd residues modulo 8. -/
theorem dyadic_supplement_bits (a : ℕ) (ha : a%2=1) :
    epsilonBit (a:ZMod 8)=signBit (χ₄ a) ∧
    omegaBit (a:ZMod 8)=signBit (χ₈ a) := by
  let k : Fin 8 := ⟨a%8,Nat.mod_lt a (by decide)⟩
  have hk : k.val%2=1 := by
    change (a%8)%2=1
    exact (Nat.mod_mod_of_dvd a (by decide : 2∣8)).trans ha
  have hR : (a:ZMod 8)=(k.val:ZMod 8) :=
    (ZMod.natCast_eq_natCast_iff' a k.val 8).mpr
      (by dsimp [k]; rw [Nat.mod_mod])
  have h4 : χ₄ a=χ₄ k.val := by
    rw [χ₄_nat_mod_four a,χ₄_nat_mod_four k.val]
    change χ₄ (a%4:ℕ)=χ₄ ((a%8)%4:ℕ)
    rw [Nat.mod_mod_of_dvd a (by decide : 4∣8)]
  have h8 : χ₈ a=χ₈ k.val := χ₈_nat_mod_eight a
  rw [hR,h4,h8]
  have table : ∀ i : Fin 8, i.val%2=1 →
      epsilonBit (i.val:ZMod 8)=signBit (χ₄ i.val) ∧
      omegaBit (i.val:ZMod 8)=signBit (χ₈ i.val) := by decide
  exact table k hk

theorem epsilon_is_half_cast (a : ℕ) (ha : a%2=1) :
    epsilonBit (a:ZMod 8)=(a/2:ℕ) := by
  rw [(dyadic_supplement_bits a ha).1,χ₄_eq_neg_one_pow ha,negOnePow_bit]

section Primes
variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

theorem odd_prime_mod_two (hp : p≠2) : p%2=1 := by
  exact (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp

theorem minusOne_bit_row (hp : p≠2) :
    signBit (legendreSym p (-1))=epsilonBit (p:ZMod 8) := by
  rw [legendreSym.at_neg_one hp,(dyadic_supplement_bits p (odd_prime_mod_two hp)).1]

theorem two_bit_row (hp : p≠2) :
    signBit (legendreSym p 2)=omegaBit (p:ZMod 8) := by
  rw [legendreSym.at_two hp,(dyadic_supplement_bits p (odd_prime_mod_two hp)).2]

private theorem prime_symbol_pm (hpq : p≠q) :
    legendreSym p q=1 ∨ legendreSym p q= -1 := by
  have h : (q:ZMod p)≠0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff q p).mp hz
    rcases (Nat.dvd_prime (Fact.out : q.Prime)).mp hd with h1|he
    · exact (Fact.out : p.Prime).ne_one h1
    · exact hpq he
  change quadraticChar (ZMod p) (((q:ℕ):ℤ):ZMod p)=1 ∨
    quadraticChar (ZMod p) (((q:ℕ):ℤ):ZMod p)= -1
  rw [Int.cast_natCast]
  exact quadraticChar_dichotomy h

/-- The real label does not enter here; this is the precise remaining
three-term finite cancellation for two distinct odd rational primes. -/
theorem distinct_odd_bit_sum (hp : p≠2) (hq : q≠2) (hpq : p≠q) :
    epsilonBit (p:ZMod 8)*epsilonBit (q:ZMod 8)+
      signBit (legendreSym q p)+signBit (legendreSym p q)=0 := by
  let j := p/2*(q/2)
  let z : ℤ := (-1)^j
  let a := legendreSym q p
  let b := legendreSym p q
  have hA : a=1 ∨ a= -1 := prime_symbol_pm hpq.symm
  have hB : b=1 ∨ b= -1 := prime_symbol_pm hpq
  have hZ : z=1 ∨ z= -1 := negOnePow_pm j
  have hZA : z*a=1 ∨ z*a= -1 := by
    rcases hZ with hZ|hZ <;> rcases hA with hA|hA <;> rw [hZ,hA] <;> decide
  have h : z*a*b=1 := distinct_odd_seed hp hq hpq
  have he := congrArg signBit h
  rw [signBit_mul_checked _ _ hZA hB,signBit_mul_checked _ _ hZ hA,
    show signBit (1:ℤ)=0 from rfl] at he
  change signBit ((-1:ℤ)^j)+signBit a+signBit b=0 at he
  rw [negOnePow_bit] at he
  rw [epsilon_is_half_cast p (odd_prime_mod_two hp),epsilon_is_half_cast q (odd_prime_mod_two hq)]
  simpa only [j,Nat.cast_mul,a,b] using he

end Primes

end CTPrimeReciprocityBitCancellation318

#print axioms CTPrimeReciprocityBitCancellation318.distinct_odd_bit_sum
