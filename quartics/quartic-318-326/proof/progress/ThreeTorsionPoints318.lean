module
public import ThreeTorsionIdentity318
public import TwoTorsionPoints318
public section
noncomputable section
namespace ThreeTorsionPoints318
open Polynomial WeierstrassCurve
set_option maxHeartbeats 0
variable {K:Type*} [Field K] [DecidableEq K] (A B:K)
abbrev curve := TwoTorsionPoints318.curve A B

lemma two_ne_zero (hD:IsUnit (-16*(4*A^3+27*B^2))) : (2:K)≠0 := by
  have h16:IsUnit (16:K):=by simpa only [neg_neg] using ((IsUnit.mul_iff.mp hD).1).neg
  have h2:IsUnit (2:K):=(isUnit_pow_iff (by decide:4≠0)).mp (by
    convert h16 using 1 <;> norm_num)
  exact h2.ne_zero

lemma equation {x y:K} (h:(curve A B).toAffine.Nonsingular x y) :
    y^2=x^3+A*x+B := by
  have he:=h.1
  rw [WeierstrassCurve.Affine.equation_iff] at he
  simpa [curve,TwoTorsionPoints318.curve] using he

lemma root_value (x:K) : (ThreeTorsionIdentity318.divisionPolynomial A B).IsRoot x ↔
    3*x^4+6*A*x^2+12*B*x-A^2=0 := by
  simp only [Polynomial.IsRoot.def,ThreeTorsionIdentity318.divisionPolynomial,
    eval_sub,eval_add,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat]

lemma y_ne_zero_of_root (hD:IsUnit (-16*(4*A^3+27*B^2)))
    {x y:K} (h:(curve A B).toAffine.Nonsingular x y)
    (hr:(ThreeTorsionIdentity318.divisionPolynomial A B).IsRoot x) : y≠0 := by
  have hp:=(root_value A B x).mp hr
  have he:=equation A B h
  intro hy
  have hc:x^3+A*x+B=0:=by rw [hy] at he;linear_combination -he
  have hd:4*A^3+27*B^2=0:=by
    linear_combination (-4*A-3*x^2)*hp+3*(7*A*x+9*B+3*x^3)*hc
  exact (IsUnit.mul_iff.mp hD).2.ne_zero hd

lemma nonvertical (h2:(2:K)≠0) {x y:K} (hy:y≠0) :
    y≠(curve A B).toAffine.negY x y := by
  simp only [curve,TwoTorsionPoints318.curve,WeierstrassCurve.Affine.negY,
    zero_mul,add_zero,sub_zero]
  intro hh
  have hmul:(2:K)*y=0:=by linear_combination hh
  exact (mul_ne_zero h2 hy) hmul

lemma slope {x y:K} (hn:y≠(curve A B).toAffine.negY x y) :
    (curve A B).toAffine.slope x x y y=(3*x^2+A)/(2*y) := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hn]
  simp only [curve,TwoTorsionPoints318.curve,WeierstrassCurve.Affine.negY,
    zero_mul,mul_zero,add_zero,zero_add,sub_zero]
  congr 1
  ring

/-- The literal third-division polynomial is equivalent to the actual
elliptic doubling equation P+P=-P, not a supplied order predicate. -/
theorem root_iff_double_neg (hD:IsUnit (-16*(4*A^3+27*B^2)))
    {x y:K} (h:(curve A B).toAffine.Nonsingular x y) :
    (ThreeTorsionIdentity318.divisionPolynomial A B).IsRoot x ↔
      WeierstrassCurve.Affine.Point.some x y h+
        WeierstrassCurve.Affine.Point.some x y h=
          -WeierstrassCurve.Affine.Point.some x y h := by
  have he:=equation A B h
  constructor
  · intro hr
    have hp:=(root_value A B x).mp hr
    have hy:=y_ne_zero_of_root A B hD h hr
    have hn:=nonvertical A B (x:=x) (two_ne_zero A B hD) hy
    have hden:2*y≠0:=mul_ne_zero (two_ne_zero A B hD) hy
    have hs:((curve A B).toAffine.slope x x y y)^2=3*x:=by
      rw [slope A B hn,div_pow]
      apply (div_eq_iff (pow_ne_zero 2 hden)).mpr
      linear_combination -hp-12*x*he
    have hx:(curve A B).toAffine.addX x x ((curve A B).toAffine.slope x x y y)=x:=by
      simp only [WeierstrassCurve.Affine.addX,curve,TwoTorsionPoints318.curve,
        zero_mul,add_zero,sub_zero] at hs ⊢
      linear_combination hs
    have hyadd:(curve A B).toAffine.addY x x y
        ((curve A B).toAffine.slope x x y y)=(curve A B).toAffine.negY x y:=by
      simp only [WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,hx,
        sub_self,mul_zero,zero_add]
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hn,
      WeierstrassCurve.Affine.Point.neg_some,WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx,hyadd⟩
  · intro hdbl
    have hn:y≠(curve A B).toAffine.negY x y:=by
      intro hzero
      rw [WeierstrassCurve.Affine.Point.add_self_of_Y_eq hzero] at hdbl
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ (neg_eq_zero.mp hdbl.symm)
    have hy:y≠0:=by
      intro hz
      apply hn
      simp [hz,curve,TwoTorsionPoints318.curve,WeierstrassCurve.Affine.negY]
    have hden:2*y≠0:=mul_ne_zero (two_ne_zero A B hD) hy
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hn,
      WeierstrassCurve.Affine.Point.neg_some,WeierstrassCurve.Affine.Point.some.injEq] at hdbl
    have hs:((curve A B).toAffine.slope x x y y)^2=3*x:=by
      have hx:=hdbl.1
      simp only [WeierstrassCurve.Affine.addX,curve,TwoTorsionPoints318.curve,
        zero_mul,add_zero,sub_zero] at hx ⊢
      linear_combination hx
    rw [slope A B hn,div_pow] at hs
    have hnum:=(div_eq_iff (pow_ne_zero 2 hden)).mp hs
    apply (root_value A B x).mpr
    linear_combination -hnum-12*x*he

/-- Exact order three for field-valued points of the actual short elliptic curve. -/
theorem root_iff_order_three (hD:IsUnit (-16*(4*A^3+27*B^2)))
    {x y:K} (h:(curve A B).toAffine.Nonsingular x y) :
    (ThreeTorsionIdentity318.divisionPolynomial A B).IsRoot x ↔
      addOrderOf (WeierstrassCurve.Affine.Point.some x y h)=3 := by
  letI:Fact (Nat.Prime 3):=⟨by decide⟩
  rw [root_iff_double_neg A B hD h,addOrderOf_eq_prime_iff]
  have hs:(3:ℕ)=2+1:=rfl
  simp only [hs,add_nsmul,two_nsmul,one_nsmul]
  constructor
  · intro hh
    exact ⟨by rw [hh,neg_add_cancel],WeierstrassCurve.Affine.Point.some_ne_zero _⟩
  · rintro ⟨hh,_⟩
    exact eq_neg_iff_add_eq_zero.mpr hh

end ThreeTorsionPoints318
