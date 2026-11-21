module
public import CTDyadicSourceTorsionImage318
public import ActualTwoDescentEllipticModel318
import all ActualTwoDescentEllipticModel318
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
public section

noncomputable section

namespace CTDyadicActualSourceClasses318

open ActualTwoDescentEllipticModel318 ActualTwoDescentSquareClassQuotient318
open CTRetainedDyadicTorsionClasses318 CTDyadicSourceTorsionImage318

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : DecidableEq ℚ_[2] := Classical.decEq _

/-- Literal source x-class with its correct values at O and (0,0). This
is a point-set statement, not yet a named dual-isogeny quotient map. -/
def sourceXClass (n : ℕ) (hn : 0<n) : Point (n:ℚ_[2]) → SquareClass ℚ_[2]
  | .zero => 1
  | .some x _ _ =>
    if hx : x=0 then
      classOf (-3*(n:ℚ_[2])^2)
        (mul_ne_zero (by norm_num) (pow_ne_zero _ (Nat.cast_ne_zero.mpr hn.ne')))
    else classOf x hx

theorem actual_source_range_eq_torsion (n : ℕ) (hn : 0<n)
    (hr : (n:ZMod 12)=11) :
    Set.range (sourceXClass n hn) = Set.range (torsionClass n hr) := by
  have hn0 : (n:ℚ_[2])≠0 := Nat.cast_ne_zero.mpr hn.ne'
  have ht : (-3*(n:ℚ_[2]))≠0 := mul_ne_zero (by norm_num) hn0
  have h0 := torsionClass_zero n hr
  have hK := torsionClass_kernel n hn hr
  have hF := torsionClass_first n hn hr
  have hL := torsionClass_last n hn hr
  apply Set.Subset.antisymm
  · rintro _ ⟨P,rfl⟩
    cases P with
    | zero => exact ⟨(false,false),h0⟩
    | some x y hxy =>
      by_cases hx : x=0
      · exact ⟨(false,true),by simpa only [sourceXClass,dif_pos hx] using hK⟩
      · have he := (curve_equation (n:ℚ_[2]) x y).mp hxy.left
        obtain ⟨i,hi⟩ := actual_source_affine_class_is_torsion n hn hr x y hx he
        exact ⟨i,by simpa only [sourceXClass,dif_neg hx] using hi.symm⟩
  · rintro _ ⟨⟨i,j⟩,rfl⟩
    cases i <;> cases j
    · exact ⟨WeierstrassCurve.Affine.Point.zero,h0.symm⟩
    · refine ⟨point (n:ℚ_[2]) 0 0 hn0 (by simp),?_⟩
      simpa only [point,sourceXClass,dif_pos rfl] using hK.symm
    · refine ⟨point (n:ℚ_[2]) n 0 hn0 (by simp),?_⟩
      simpa only [point,sourceXClass,dif_neg hn0] using hF.symm
    · refine ⟨point (n:ℚ_[2]) (-3*n) 0 hn0 (by ring),?_⟩
      simpa only [point,sourceXClass,dif_neg ht] using hL.symm

end CTDyadicActualSourceClasses318

#print axioms CTDyadicActualSourceClasses318.actual_source_range_eq_torsion
