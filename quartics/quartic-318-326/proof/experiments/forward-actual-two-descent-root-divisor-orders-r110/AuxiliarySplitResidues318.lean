module
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.Tactic
public section
namespace AuxiliarySplitResidues318

/-- Simultaneous splitting of2 and6 forces the residue ±1 modulo24.
The denominator may be any odd natural, including1; no prime or hidden
coprimality premise is needed. This applies to the finite parity product
once its two Jacobi values have actually been established. -/
theorem residue_twentyfour (n : ℕ) (hn : Odd n)
    (h2 : jacobiSym 2 n=1) (h6 : jacobiSym 6 n=1) :
    n%24=1 ∨ n%24=23 := by
  have h3 : jacobiSym 3 n=1 := by
    have hh := jacobiSym.mul_left 2 3 n
    norm_num only [show (2:ℤ)*3=6 by norm_num,h6,h2,one_mul] at hh
    exact hh.symm
  have hc2 := jacobiSym.at_two hn
  rw [ZMod.χ₈_nat_eq_if_mod_eight,h2] at hc2
  have hr := jacobiSym.quadratic_reciprocity_if
    (a:=3) (b:=n) (by decide) (Nat.odd_iff.mp hn)
  simp only [Nat.cast_ofNat] at hr
  rw [h3,jacobiSym.mod_left (n:ℤ) 3,←Int.natCast_mod] at hr
  have hj0 : jacobiSym 0 3=0 := jacobiSym.zero_left (by decide)
  have hj2 : jacobiSym 2 3= -1 := by
    rw [jacobiSym.at_two (by decide : Odd 3),ZMod.χ₈_nat_eq_if_mod_eight]
    norm_num
  have h2r : n%2=(n%24)%2 := (Nat.mod_mod_of_dvd n (by decide : 2∣24)).symm
  have h3r : n%3=(n%24)%3 := (Nat.mod_mod_of_dvd n (by decide : 3∣24)).symm
  have h4r : n%4=(n%24)%4 := (Nat.mod_mod_of_dvd n (by decide : 4∣24)).symm
  have h8r : n%8=(n%24)%8 := (Nat.mod_mod_of_dvd n (by decide : 8∣24)).symm
  rw [h2r,h8r] at hc2
  rw [h3r,h4r] at hr
  have hlt := Nat.mod_lt n (by decide : 0<24)
  interval_cases he : n%24 <;> norm_num [he,hj0,hj2] at hc2 hr ⊢

end AuxiliarySplitResidues318
