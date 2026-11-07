module
public import TangentCoordinates318
public import Mathlib.Analysis.Normed.Operator.Mul
public section
noncomputable section
namespace ComplexQuadraticForms318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

/-- Every genuine continuous complex bilinear form on a one-dimensional
complex vector space is determined by its value at (1,1). -/
theorem bilinear_formula (B:ℂ→L[ℂ]ℂ→L[ℂ]ℂ) (u v:ℂ) :
    B u v=B 1 1*u*v := by
  have hu:B u=u • B 1 := by
    simpa only [smul_eq_mul,mul_one] using (map_smul B u (1:ℂ))
  have hv:B 1 v=v • B 1 1 := by
    simpa only [smul_eq_mul,mul_one] using (map_smul (B 1) v (1:ℂ))
  rw [hu,smul_apply,hv]
  simp only [smul_eq_mul]
  ring

@[expose] def coefficientEquiv : ℂ ≃ₗ[ℂ] (ℂ→L[ℂ]ℂ→L[ℂ]ℂ) where
  toFun q:=q • ContinuousLinearMap.mul ℂ ℂ
  invFun B:=B 1 1
  left_inv q:=by simp
  right_inv B:=by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply,ContinuousLinearMap.mul_apply',smul_eq_mul]
    simpa only [mul_assoc] using (bilinear_formula B u v).symm
  map_add' q r:=by exact add_smul q r (ContinuousLinearMap.mul ℂ ℂ)
  map_smul' c q:=by simp only [RingHom.id_apply,smul_eq_mul,mul_smul]

theorem coefficientEquiv_apply (q u v:ℂ) : coefficientEquiv q u v=q*u*v := by
  simp only [coefficientEquiv,LinearEquiv.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,
    smul_apply,ContinuousLinearMap.mul_apply',smul_eq_mul,mul_assoc]

theorem symmetric (B:ℂ→L[ℂ]ℂ→L[ℂ]ℂ) (u v:ℂ) : B u v=B v u := by
  rw [bilinear_formula B u v,bilinear_formula B v u]
  ring

end ComplexQuadraticForms318
