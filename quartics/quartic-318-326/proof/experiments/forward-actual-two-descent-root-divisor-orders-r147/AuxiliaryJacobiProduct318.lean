module
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Tactic
public section
namespace AuxiliaryJacobiProduct318
open Nat ZMod

/-- The pair of reciprocal Jacobi factors, with its exact sign. -/
theorem reciprocal_product (P U : ℕ) (hP : Odd P) (hU : Odd U)
    (hcop : (U:ℤ).gcd P=1) :
    jacobiSym (U:ℤ) P*jacobiSym (P:ℤ) U=
      if P%4=3 ∧ U%4=3 then -1 else 1 := by
  have hs := jacobiSym.sq_one hcop
  have hr := jacobiSym.quadratic_reciprocity_if
    (Nat.odd_iff.mp hP) (Nat.odd_iff.mp hU)
  by_cases h : P%4=3 ∧ U%4=3
  · simp only [h,and_self,ite_true] at hr ⊢
    rw [←hr]
    nlinarith [hs]
  · simp only [h,ite_false] at hr ⊢
    rw [←hr]
    nlinarith [hs]

/-- The sign product occurring after multiplying the local conditions at
primes dividing P and U. The two alternatives encode a positive C=1 mod4,
or a negative C=1 mod4 whose real binary form forces sigma=-1.
Neither the local conditions nor a prime in their residue class is assumed
produced by this purely finite reciprocity calculation. -/
theorem real_compatible_sign_product (P U : ℕ) (hP : Odd P) (hU : Odd U)
    (hcop : (U:ℤ).gcd P=1) (epsilon sigma : ℤ)
    (hsigma : sigma=1 ∨ sigma= -1)
    (hsign : (epsilon=1 ∧ (P*U)%4=1) ∨
      (epsilon= -1 ∧ (P*U)%4=3 ∧ sigma= -1)) :
    jacobiSym (epsilon*sigma) P*jacobiSym (-sigma) U*
      jacobiSym (U:ℤ) P*jacobiSym (P:ℤ) U=1 := by
  have hP4 := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hP)
  have hU4 := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hU)
  have hneg (n : ℕ) (hn : Odd n) :
      jacobiSym (-1) n = if n%4=1 then 1 else -1 := by
    rw [jacobiSym.at_neg_one hn]
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn) with h | h
    · rw [χ₄_nat_one_mod_four h]
      simp only [h,ite_true]
    · rw [χ₄_nat_three_mod_four h]
      norm_num [h]
  calc
    _=(jacobiSym (epsilon*sigma) P*jacobiSym (-sigma) U)*
        (jacobiSym (U:ℤ) P*jacobiSym (P:ℤ) U) := by ring
    _=1 := by
      rw [reciprocal_product P U hP hU hcop]
      rcases hsign with ⟨rfl,hN⟩ | ⟨rfl,hN,rfl⟩
      · rcases hsigma with rfl | rfl <;>
          rcases hP4 with hP4 | hP4 <;> rcases hU4 with hU4 | hU4 <;>
          simp_all [Nat.mul_mod,jacobiSym.one_left,hneg P hP,hneg U hU]
      · rcases hP4 with hP4 | hP4 <;> rcases hU4 with hU4 | hU4 <;>
          simp_all [Nat.mul_mod,jacobiSym.one_left,hneg P hP,hneg U hU]

end AuxiliaryJacobiProduct318
