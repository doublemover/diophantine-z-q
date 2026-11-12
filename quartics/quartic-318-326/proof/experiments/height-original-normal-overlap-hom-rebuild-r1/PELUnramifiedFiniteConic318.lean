module
public import PELActualRamifiedQuaternion318
public import Mathlib.FieldTheory.Finite.Basic
public section
noncomputable section
namespace PELUnramifiedFiniteConic318
open Polynomial
set_option maxHeartbeats 1000000

/-- The same conic used by the actual quaternion presentation has a point
over every odd residue field where its coefficient 210 is nonzero. -/
theorem finite_conic (p : ℕ) [hp : Fact p.Prime] (hp210 : ¬p ∣ 210) :
    ∃ x y : ZMod p, x^2+210*y^2=5 := by
  have h210 : (210 : ZMod p)≠0 := by
    intro h
    exact hp210 ((CharP.cast_eq_zero_iff (ZMod p) p 210).mp h)
  have hp2 : p≠2 := by
    intro h
    subst p
    exact hp210 (by decide)
  have hodd : p%2=1 := (hp.1.eq_two_or_odd.resolve_left hp2)
  let f : (ZMod p)[X] := X^2
  let g : (ZMod p)[X] := C (210:ZMod p)*(X^2-C (5/210))
  have hg : g.degree=2 := by
    dsimp [g]
    rw [degree_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr h210),
      degree_X_pow_sub_C (by decide)]
  obtain ⟨x,y,hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f:=f) (g:=g) (degree_X_pow 2) hg (by simpa using hodd)
  refine ⟨x,y,?_⟩
  simp only [f,g,eval_mul,eval_C,eval_sub,eval_pow,eval_X] at hxy
  have hc : (210:ZMod p)*(5/210)=5 := by field_simp [h210]
  linear_combination hxy+hc

/-- At least one of the actual conic derivatives is nonzero. This is the
precise input to the p-adic lift, rather than an assumed smooth point. -/
theorem finite_smooth_conic (p : ℕ) [Fact p.Prime] (hp210 : ¬p ∣ 210) :
    ∃ x y : ZMod p, x^2+210*y^2=5 ∧ (2*x≠0 ∨ 420*y≠0) := by
  obtain ⟨x,y,hxy⟩ := finite_conic p hp210
  have h210 : (210:ZMod p)≠0 := by
    exact fun h => hp210 ((CharP.cast_eq_zero_iff (ZMod p) p 210).mp h)
  have h2 : (2:ZMod p)≠0 := by
    intro h
    apply h210
    calc (210:ZMod p)=2*105 := by norm_num
         _ = 0 := by rw [h,zero_mul]
  have h5 : (5:ZMod p)≠0 := by
    intro h
    apply h210
    calc (210:ZMod p)=5*42 := by norm_num
         _ = 0 := by rw [h,zero_mul]
  refine ⟨x,y,hxy,?_⟩
  by_cases hx : x=0
  · right
    have hy : y≠0 := by
      intro hy
      apply h5
      simpa [hx,hy] using hxy.symm
    have h420 : (420:ZMod p)≠0 := by
      convert mul_ne_zero h2 h210 using 1 <;> norm_num
    exact mul_ne_zero h420 hy
  · exact Or.inl (mul_ne_zero h2 hx)
end PELUnramifiedFiniteConic318
