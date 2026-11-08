module
public import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Tactic
public section
noncomputable section
namespace ShortScaling318
set_option maxHeartbeats 0
variable {K : Type*} [Field K] [DecidableEq K]
  (W W' : WeierstrassCurve K) [W.IsShortNF] [W'.IsShortNF]
  [W.IsElliptic] [W'.IsElliptic] (u : Kˣ)
  (h4 : W'.a₄ = (u:K)^4 * W.a₄) (h6 : W'.a₆ = (u:K)^6 * W.a₆)

include h4 h6 in
lemma equation_scale (x y : K) :
    W'.toAffine.Equation ((u:K)^2*x) ((u:K)^3*y) ↔ W.toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff', WeierstrassCurve.Affine.equation_iff']
  simp only [WeierstrassCurve.a₁_of_isShortNF, WeierstrassCurve.a₂_of_isShortNF,
    WeierstrassCurve.a₃_of_isShortNF, h4, h6]
  have he : ((u:K)^3*y)^2+0*((u:K)^2*x)*((u:K)^3*y)+0*((u:K)^3*y)-
      (((u:K)^2*x)^3+0*((u:K)^2*x)^2+((u:K)^4*W.a₄)*((u:K)^2*x)+(u:K)^6*W.a₆) =
      (u:K)^6*(y^2+0*x*y+0*y-(x^3+0*x^2+W.a₄*x+W.a₆)) := by ring
  rw [he,mul_eq_zero]
  simp [Units.ne_zero u]

lemma negY_scale (x y : K) :
    W'.toAffine.negY ((u:K)^2*x) ((u:K)^3*y) = (u:K)^3 * W.toAffine.negY x y := by
  simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.a₁_of_isShortNF,
    WeierstrassCurve.a₃_of_isShortNF]
  ring

lemma vertical_iff (x₁ x₂ y₁ y₂ : K) :
    ((u:K)^2*x₁ = (u:K)^2*x₂ ∧
      (u:K)^3*y₁ = W'.toAffine.negY ((u:K)^2*x₂) ((u:K)^3*y₂)) ↔
      (x₁=x₂ ∧ y₁=W.toAffine.negY x₂ y₂) := by
  rw [negY_scale W W' u]
  simp only [mul_right_inj' (pow_ne_zero 2 (Units.ne_zero u)),
    mul_right_inj' (pow_ne_zero 3 (Units.ne_zero u))]

include h4 in
lemma slope_scale (x₁ x₂ y₁ y₂ : K) :
    W'.toAffine.slope ((u:K)^2*x₁) ((u:K)^2*x₂) ((u:K)^3*y₁) ((u:K)^3*y₂) =
      (u:K) * W.toAffine.slope x₁ x₂ y₁ y₂ := by
  simp only [WeierstrassCurve.Affine.slope, negY_scale W W' u,
    mul_right_inj' (pow_ne_zero 2 (Units.ne_zero u)),
    mul_right_inj' (pow_ne_zero 3 (Units.ne_zero u))]
  split_ifs with hx hy
  · simp
  · simp only [WeierstrassCurve.a₁_of_isShortNF, WeierstrassCurve.a₂_of_isShortNF,
      WeierstrassCurve.Affine.negY, WeierstrassCurve.a₃_of_isShortNF,h4]
    simp only [zero_mul, mul_zero, add_zero, sub_zero]
    rw [show 3*((u:K)^2*x₁)^2+(u:K)^4*W.a₄ = (u:K)^4*(3*x₁^2+W.a₄) by ring,
      ←mul_sub]
    rw [mul_div_mul_comm]
    congr 1
    field_simp [Units.ne_zero u]
    <;> ring
  · rw [←mul_sub, ←mul_sub, mul_div_mul_comm]
    congr 1
    field_simp [Units.ne_zero u]
    <;> ring

lemma addX_scale (x₁ x₂ l : K) :
    W'.toAffine.addX ((u:K)^2*x₁) ((u:K)^2*x₂) ((u:K)*l) =
      (u:K)^2 * W.toAffine.addX x₁ x₂ l := by
  simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.a₁_of_isShortNF,
    WeierstrassCurve.a₂_of_isShortNF]
  ring

lemma addY_scale (x₁ x₂ y₁ l : K) :
    W'.toAffine.addY ((u:K)^2*x₁) ((u:K)^2*x₂) ((u:K)^3*y₁) ((u:K)*l) =
      (u:K)^3 * W.toAffine.addY x₁ x₂ y₁ l := by
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX,
    WeierstrassCurve.a₁_of_isShortNF, WeierstrassCurve.a₂_of_isShortNF,
    WeierstrassCurve.a₃_of_isShortNF]
  ring

@[expose] def pointMap : W.toAffine.Point → W'.toAffine.Point
  | .zero => .zero
  | .some x y h => .mk ((equation_scale W W' u h4 h6 x y).mpr h.1)

@[expose] def pointInverse : W'.toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .mk ((equation_scale W W' u h4 h6 (x/(u:K)^2) (y/(u:K)^3)).mp
      (by simpa [mul_div_cancel₀, Units.ne_zero u] using h.1))

@[expose] def pointEquiv : W.toAffine.Point ≃ W'.toAffine.Point where
  toFun := pointMap W W' u h4 h6
  invFun := pointInverse W W' u h4 h6
  left_inv P := by
    cases P with
    | zero => rfl
    | some x y h => simp [pointMap, pointInverse, WeierstrassCurve.Affine.Point.mk,
        Units.ne_zero u]
  right_inv P := by
    cases P with
    | zero => rfl
    | some x y h => simp [pointMap, pointInverse, WeierstrassCurve.Affine.Point.mk,
        mul_div_cancel₀, Units.ne_zero u]

lemma pointMap_add (P Q : W.toAffine.Point) :
    pointMap W W' u h4 h6 (P+Q) = pointMap W W' u h4 h6 P + pointMap W W' u h4 h6 Q := by
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => rfl
    | some x₂ y₂ h₂ =>
      by_cases hv : x₁=x₂ ∧ y₁=W.toAffine.negY x₂ y₂
      · have hv' := (vertical_iff W W' u x₁ x₂ y₁ y₂).mpr hv
        simp only [WeierstrassCurve.Affine.Point.add_of_Y_eq hv.1 hv.2,
          pointMap, WeierstrassCurve.Affine.Point.mk,
          WeierstrassCurve.Affine.Point.add_of_Y_eq hv'.1 hv'.2]
        rfl
      · have hv' := mt (vertical_iff W W' u x₁ x₂ y₁ y₂).mp hv
        simp only [WeierstrassCurve.Affine.Point.add_some hv, pointMap,
          WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.add_some hv']
        rw [WeierstrassCurve.Affine.Point.some.injEq]
        exact ⟨(by rw [slope_scale W W' u h4, addX_scale W W' u]),
          (by rw [slope_scale W W' u h4, addY_scale W W' u])⟩

/-- Actual chord-and-tangent addition is preserved by coordinate scaling. -/
@[expose] def pointAddEquiv : W.toAffine.Point ≃+ W'.toAffine.Point :=
  { pointEquiv W W' u h4 h6 with map_add' := pointMap_add W W' u h4 h6 }

/-- A change of variables between short models in characteristic zero is a
pure scaling. This construction consumes actual equality of algebraic j. -/
theorem exists_scaling_of_j_eq [CharZero K] [IsSepClosed K] (hj : W.j = W'.j) :
    ∃ v : Kˣ, W'.a₄ = (v:K)^4 * W.a₄ ∧ W'.a₆ = (v:K)^6 * W.a₆ := by
  obtain ⟨C,hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq W W' hj
  have hs : C.s = 0 := by
    have hh := congrArg WeierstrassCurve.a₁ hC
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.a₁_of_isShortNF,
      zero_add] at hh
    have hz := (mul_eq_zero.mp hh).resolve_left (Units.ne_zero C.u⁻¹)
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have hr : C.r = 0 := by
    have hh := congrArg WeierstrassCurve.a₂ hC
    simp only [WeierstrassCurve.variableChange_a₂, WeierstrassCurve.a₁_of_isShortNF,
      WeierstrassCurve.a₂_of_isShortNF,hs,zero_mul,sub_zero,zero_add,zero_pow (by decide : 2≠0)] at hh
    have hz := (mul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 (Units.ne_zero C.u⁻¹))
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have ht : C.t = 0 := by
    have hh := congrArg WeierstrassCurve.a₃ hC
    simp only [WeierstrassCurve.variableChange_a₃, WeierstrassCurve.a₁_of_isShortNF,
      WeierstrassCurve.a₃_of_isShortNF,hr,zero_mul,zero_add] at hh
    have hz := (mul_eq_zero.mp hh).resolve_left (pow_ne_zero 3 (Units.ne_zero C.u⁻¹))
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  refine ⟨C.u⁻¹, ?_, ?_⟩
  · simpa [WeierstrassCurve.variableChange_a₄,hs,hr,ht] using
      (congrArg WeierstrassCurve.a₄ hC).symm
  · simpa [WeierstrassCurve.variableChange_a₆,hs,hr,ht] using
      (congrArg WeierstrassCurve.a₆ hC).symm

end ShortScaling318
