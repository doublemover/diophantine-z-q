module
public import ShortTwoTorsion318
public section
noncomputable section
namespace TwoTorsionPoints318
open Polynomial WeierstrassCurve
set_option maxHeartbeats 0
variable {K:Type*} [Field K] [DecidableEq K] (A B:K)

@[expose] def curve : WeierstrassCurve K:=⟨0,0,0,A,B⟩
lemma discriminant : (curve A B).Δ= -16*(4*A^3+27*B^2) := by
  simp only [curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

lemma root_equation (x:K) :
    (ShortTwoTorsion318.polynomial A B).IsRoot x ↔ (curve A B).toAffine.Equation x 0 := by
  rw [Polynomial.IsRoot.def,WeierstrassCurve.Affine.equation_iff]
  simp only [ShortTwoTorsion318.polynomial,eval_add,eval_pow,eval_X,eval_mul,eval_C,
    curve,zero_pow (by decide:2≠0),zero_mul,zero_add,add_zero]
  exact eq_comm

/-- Every point represented by the cubic is an actual elliptic point of exact
order two, and every nonsingular zero-y point is represented by it. -/
theorem root_iff_order_two (hD:IsUnit (-16*(4*A^3+27*B^2))) (x:K) :
    (ShortTwoTorsion318.polynomial A B).IsRoot x ↔
      ∃h:(curve A B).toAffine.Nonsingular x 0,
        addOrderOf (WeierstrassCurve.Affine.Point.some x 0 h)=2 := by
  letI:Fact (Nat.Prime 2):=⟨by decide⟩
  constructor
  · intro hx
    have hd:(curve A B).Δ≠0:=by rw [discriminant];exact hD.ne_zero
    have hns:=((curve A B).toAffine.equation_iff_nonsingular_of_Δ_ne_zero hd).mp
      ((root_equation A B x).mp hx)
    refine ⟨hns,addOrderOf_eq_prime ?_ (WeierstrassCurve.Affine.Point.some_ne_zero _)⟩
    rw [two_nsmul]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
    simp [WeierstrassCurve.Affine.negY,curve]
  · rintro ⟨h,_⟩
    exact (root_equation A B x).mpr h.1

/-- Any actual nonzero affine point of exact order two has y=0, so it lies in
the constructed cubic cover. This uses the real elliptic group law on K-points. -/
theorem order_two_zero_y (hD:IsUnit (-16*(4*A^3+27*B^2)))
    {x y:K} (h:(curve A B).toAffine.Nonsingular x y)
    (horder:addOrderOf (WeierstrassCurve.Affine.Point.some x y h)=2) : y=0 := by
  letI:Fact (Nat.Prime 2):=⟨by decide⟩
  have hadd:=((addOrderOf_eq_prime_iff).mp horder).1
  rw [two_nsmul] at hadd
  have hy:y=(curve A B).toAffine.negY x y:=by
    by_contra hne
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne] at hadd
    exact WeierstrassCurve.Affine.Point.some_ne_zero _ hadd
  have h16:IsUnit (-16:K):=(IsUnit.mul_iff.mp hD).1
  have h2:IsUnit (2:K):=(isUnit_pow_iff (by decide:4≠0)).mp (by
    convert h16.neg using 1 <;> norm_num)
  have hy0:(2:K)*y=0:=by
    simp only [curve,WeierstrassCurve.Affine.negY,zero_mul,add_zero,sub_zero] at hy
    linear_combination hy
  exact (mul_eq_zero.mp hy0).resolve_left h2.ne_zero

end TwoTorsionPoints318
