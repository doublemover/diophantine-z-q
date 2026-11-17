module
public import LegendrePadicResidueDepth318
public import LegendreDyadicNormTables318
public section
namespace AuxiliaryDyadicValue318
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- An actual dyadic affine norm supplies the primitive mod8 table input.
The denominator being odd is a consequence of the residue table, not an input. -/
theorem unit_class_of_local_norm (a t : ℤ) (ha : a%8=2 ∨ a%8=6)
    (ht : Odd t) (x z : ℚ_[2]) (h : z^2-(a:ℚ_[2])*x^2=(t:ℚ_[2])) :
    t%8=1 ∨ t%8=(1-a)%8 := by
  obtain ⟨X,Z,W,hcong,hprim⟩ :=
    LegendrePadicResidueDepth318.residues_of_local_solution 2 3 (by decide)
      a t x z 1 (by simp) (by simpa using sub_eq_zero.mpr h)
  apply LegendreDyadicNormTables318.unit_norm_table a t X Z W ha ht
  · simpa only [Nat.cast_ofNat,show (2:ℤ)^3=8 by norm_num] using hcong
  · exact hprim

/-- The even local norm is reduced modulo16 before the odd-part table is used. -/
theorem even_class_of_local_norm (a v : ℤ) (ha : a%16=2 ∨ a%16=6)
    (hv : Odd v) (x z : ℚ_[2]) (h : z^2-(a:ℚ_[2])*x^2=((2*v:ℤ):ℚ_[2])) :
    v%8=7 ∨ v%8=a%16-1 := by
  obtain ⟨X,Z,W,hcong,hprim⟩ :=
    LegendrePadicResidueDepth318.residues_of_local_solution 2 4 (by decide)
      a (2*v) x z 1 (by simp) (by simpa using sub_eq_zero.mpr h)
  apply LegendreDyadicNormTables318.even_norm_table a v X Z W ha hv
  · simpa only [Nat.cast_ofNat,show (2:ℤ)^4=16 by norm_num] using hcong
  · exact hprim

/-- The two actual binary norm equations force a unit common value to be1 mod8.
Only the prepared coefficient congruence is supplied; no dyadic square root
of C or primitive residue vector is assumed. -/
theorem unit_common_value (C t : ℤ) (hC : C%8=1) (ht : Odd t)
    (X Z T Y : ℚ_[2])
    (hA : X^2-2*Z^2=(t:ℚ_[2]))
    (hB : (C:ℚ_[2])*T^2-6*Y^2=(t:ℚ_[2])) : t%8=1 := by
  have hAt := unit_class_of_local_norm 2 t (Or.inl (by norm_num)) ht Z X
    (by simpa using hA)
  have hCo : Odd C := Int.odd_iff.mpr (by omega)
  have hBt : ((C:ℚ_[2])*T)^2-((6*C:ℤ):ℚ_[2])*Y^2=((C*t:ℤ):ℚ_[2]) := by
    push_cast
    linear_combination (C:ℚ_[2])*hB
  have hCt := unit_class_of_local_norm (6*C) (C*t)
    (Or.inr (by omega)) (hCo.mul ht) Y ((C:ℚ_[2])*T) hBt
  have hm : (C*t)%8=t%8 := by simp [Int.mul_emod,hC]
  omega

/-- For an even common value2v with v odd, the two norm equations force
v=7 mod8. Both even tables use mod16; division by2 is not performed first. -/
theorem even_common_value (C v : ℤ) (hC : C%8=1) (hv : Odd v)
    (X Z T Y : ℚ_[2])
    (hA : X^2-2*Z^2=((2*v:ℤ):ℚ_[2]))
    (hB : (C:ℚ_[2])*T^2-6*Y^2=((2*v:ℤ):ℚ_[2])) : v%8=7 := by
  have hAt := even_class_of_local_norm 2 v (Or.inl (by norm_num)) hv Z X
    (by simpa using hA)
  have hCo : Odd C := Int.odd_iff.mpr (by omega)
  have hBt : ((C:ℚ_[2])*T)^2-((6*C:ℤ):ℚ_[2])*Y^2=((2*(C*v):ℤ):ℚ_[2]) := by
    push_cast at hB ⊢
    linear_combination (C:ℚ_[2])*hB
  have hCt := even_class_of_local_norm (6*C) (C*v)
    (Or.inr (by omega)) (hCo.mul hv) Y ((C:ℚ_[2])*T) hBt
  have hm : (C*v)%8=v%8 := by simp [Int.mul_emod,hC]
  have hc16 : (6*C)%16=6 := by omega
  omega

end AuxiliaryDyadicValue318
