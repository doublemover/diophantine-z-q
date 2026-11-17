module
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Tactic
public section
namespace AuxiliaryComplementCharacters318

/-- The supplementary law at either actual signed residue modulo8. -/
theorem two_of_residue (n : ℕ) (h : n%8=1 ∨ n%8=7) : jacobiSym 2 n=1 := by
  have hn : Odd n := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.at_two hn,ZMod.χ₈_nat_eq_if_mod_eight]
  rcases h with h | h <;> norm_num [h,Nat.odd_iff.mp hn]

/-- C=1 mod24 and the selected P-character determine the complementary
character. No separate splitting2 hypothesis for U is supplied. -/
theorem two_complement (C : ℤ) (P U : ℕ) (hC : C%24=1)
    (hN : C.natAbs=P*U) (hP : jacobiSym 2 P=1) : jacobiSym 2 U=1 := by
  have hC0 : C≠0 := by intro h; subst C; norm_num at hC
  have hN0 : C.natAbs≠0 := Int.natAbs_ne_zero.mpr hC0
  have hP0 : P≠0 := by intro h; rw [h,zero_mul] at hN; exact hN0 hN
  have hU0 : U≠0 := by intro h; rw [h,mul_zero] at hN; exact hN0 hN
  have hN8 : C.natAbs%8=1 ∨ C.natAbs%8=7 := by
    rcases Int.natAbs_eq C with he | he
    · have hh : (C.natAbs:ℤ)%8=1 := by rw [←he]; omega
      exact Or.inl (by exact_mod_cast hh)
    · have hh : (C.natAbs:ℤ)%8=7 := by
        have hc : (-(C.natAbs:ℤ))%8=1 := by rw [←he]; omega
        omega
      exact Or.inr (by exact_mod_cast hh)
  have hh := two_of_residue C.natAbs hN8
  rw [hN,jacobiSym.mul_right' 2 hP0 hU0,hP,one_mul] at hh
  exact hh

/-- Both required splitting characters follow from the same residue ±1
mod24. This includes n=1 and uses no primality premise. -/
theorem six_of_twentyfour (n : ℕ) (h : n%24=1 ∨ n%24=23) : jacobiSym 6 n=1 := by
  have hn : Odd n := Nat.odd_iff.mpr (by omega)
  have hm : jacobiSym 6 n=jacobiSym 6 (n%24) := by
    simpa using jacobiSym.mod_right 6 hn
  rw [hm]
  rcases h with h | h <;> rw [h] <;> norm_num

/-- The already-derived dyadic odd-part and3-adic unit conditions force
q=±1 mod24 when the selected odd product P is ±1 mod24. This is the exact
finite residue calculation needed before the new-prime character. -/
theorem prime_residue_of_common_value (σ : ℤ) (P q α : ℕ)
    (hσ : σ=1 ∨ σ= -1) (hP : P%24=1 ∨ P%24=23) (hα : α=0 ∨ α=1)
    (hdyadic : if α=0 then (σ*(P:ℤ)*(q:ℤ))%8=1 else (σ*(P:ℤ)*(q:ℤ))%8=7)
    (hthree : (σ*(2:ℤ)^α*(P:ℤ)*(q:ℤ))%3=1) :
    q%24=1 ∨ q%24=23 := by
  have hv : (σ*(P:ℤ)*(q:ℤ))%24=1 ∨ (σ*(P:ℤ)*(q:ℤ))%24=23 := by
    rcases hα with rfl | rfl
    · simp only [if_pos rfl,pow_zero,mul_one] at hdyadic hthree
      exact Or.inl (by omega)
    · simp only [show (1:ℕ)≠0 by decide,if_false,pow_one] at hdyadic hthree
      have he : σ*(2:ℤ)*(P:ℤ)*(q:ℤ)=2*(σ*(P:ℤ)*(q:ℤ)) := by ring
      rw [he] at hthree
      exact Or.inr (by omega)
  have hPZ : (P:ℤ)%24=1 ∨ (P:ℤ)%24=23 := by exact_mod_cast hP
  have hlo := Int.emod_nonneg (q:ℤ) (by norm_num : (24:ℤ)≠0)
  have hhi := Int.emod_lt_of_pos (q:ℤ) (by norm_num : (0:ℤ)<24)
  have hqZ : (q:ℤ)%24=1 ∨ (q:ℤ)%24=23 := by
    simp only [Int.mul_emod] at hv
    rcases hσ with rfl | rfl <;> rcases hPZ with hPZ | hPZ <;>
      simp only [hPZ] at hv <;> norm_num at hv <;> omega
  exact_mod_cast hqZ

end AuxiliaryComplementCharacters318
