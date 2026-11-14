module
public import ActualTwoDescentRootCoordinateProduct318
public import Mathlib.GroupTheory.QuotientGroup.Basic
public section
noncomputable section
namespace ActualTwoDescentSquareClassQuotient318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]



/-- The actual multiplicative squareclass group of nonzero field elements. -/
abbrev SquareClass (K : Type*) [Field K] := Kˣ ⧸ (powMonoidHom (α:=Kˣ) 2).range

def classOf (a : K) (ha : a ≠ 0) : SquareClass K := QuotientGroup.mk (Units.mk0 a ha)

lemma class_of_one : classOf (1 : K) one_ne_zero=1 := by
  have hu : Units.mk0 (1 : K) one_ne_zero=1 := by ext; rfl
  rw [classOf,hu]
  rfl

lemma class_of_mul (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    classOf (a*b) (mul_ne_zero ha hb)=classOf a ha*classOf b hb := by
  have hu : Units.mk0 (a*b) (mul_ne_zero ha hb)=Units.mk0 a ha*Units.mk0 b hb := by ext; rfl
  rw [classOf,hu]
  rfl

/-- Equality in the quotient is equivalent to an ACTUAL nonzero square multiplier. -/
lemma class_of_eq_iff (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    classOf a ha=classOf b hb ↔ ∃ s : K, s ≠ 0 ∧ a=b*s^2 := by
  change (QuotientGroup.mk (Units.mk0 a ha) : SquareClass K)=QuotientGroup.mk (Units.mk0 b hb) ↔ _
  rw [QuotientGroup.eq_iff_div_mem]
  constructor
  · rintro ⟨s,hs⟩
    have hv : (s : K)^2=a/b := by
      have h := congrArg (fun u : Kˣ => (u : K)) hs
      simpa only [powMonoidHom_apply,Units.val_pow_eq_pow_val,Units.val_div_eq_div_val,Units.val_mk0] using h
    refine ⟨s,s.ne_zero,?_⟩
    have he := (eq_div_iff hb).mp hv
    linear_combination -he
  · rintro ⟨s,hs,h⟩
    refine ⟨Units.mk0 s hs,?_⟩
    apply Units.ext
    change s^2=a/b
    apply (eq_div_iff hb).mpr
    linear_combination -h

lemma class_of_square (s : K) (hs : s ≠ 0) : classOf (s^2) (pow_ne_zero _ hs)=1 := by
  rw [←class_of_one]
  apply (class_of_eq_iff _ _ _ _).mpr
  exact ⟨s,hs,by ring⟩

end ActualTwoDescentSquareClassQuotient318
