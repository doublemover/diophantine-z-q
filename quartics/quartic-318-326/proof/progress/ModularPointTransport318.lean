module
public import ModularCurveChange318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public section
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups
namespace ModularPointTransport318
set_option maxHeartbeats 0
open ModularCurveChange318

/-- The transformed equation scales by the sixth power of c*tau+d. -/
theorem equation_scale (gamma:GL (Fin 2) ℝ) (hg:gamma∈modularImage)
    (tau:UpperHalfPlane) (x y:ℂ) :
    (ModularWeierstrass318.curve (gamma•tau)).toAffine.Equation
      (denom gamma tau^2*x) (denom gamma tau^3*y) ↔
    (ModularWeierstrass318.curve tau).toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff', WeierstrassCurve.Affine.equation_iff']
  simp only [ModularWeierstrass318.curve,NormalizedWeierstrass318.model,
    E4_transform gamma hg tau,E6_transform gamma hg tau]
  have he : (denom gamma tau ^ 3 * y) ^ 2 + 0 * (denom gamma tau ^ 2 * x) *
      (denom gamma tau ^ 3 * y) + 0 * (denom gamma tau ^ 3 * y) -
      ((denom gamma tau ^ 2 * x) ^ 3 + 0 * (denom gamma tau ^ 2 * x) ^ 2 +
      (-(denom gamma tau ^ 4 * ModularForm.E₄ tau) / 48) * (denom gamma tau ^ 2 * x) +
      -(denom gamma tau ^ 6 * ModularForm.E₆ tau) / 864) =
    denom gamma tau ^ 6 *
      (y ^ 2 + 0 * x * y + 0 * y - (x ^ 3 + 0 * x ^ 2 +
       (-ModularForm.E₄ tau / 48) * x + -ModularForm.E₆ tau / 864)) := by ring
  rw [he,mul_eq_zero]
  simp [pow_ne_zero 6 (denom_ne_zero gamma tau)]

@[expose] def pointMap (gamma:GL (Fin 2) ℝ) (hg:gamma∈modularImage)
    (tau:UpperHalfPlane) : (ModularWeierstrass318.curve tau).toAffine.Point →
      (ModularWeierstrass318.curve (gamma•tau)).toAffine.Point
  | .zero => .zero
  | .some x y h => .mk ((equation_scale gamma hg tau x y).2 h.1)

@[expose] def pointInverse (gamma:GL (Fin 2) ℝ) (hg:gamma∈modularImage)
    (tau:UpperHalfPlane) : (ModularWeierstrass318.curve (gamma•tau)).toAffine.Point →
      (ModularWeierstrass318.curve tau).toAffine.Point
  | .zero => .zero
  | .some x y h => .mk ((equation_scale gamma hg tau (x/denom gamma tau^2)
      (y/denom gamma tau^3)).1 (by
        simpa [mul_div_cancel₀,denom_ne_zero gamma tau] using h.1))

@[expose] def pointEquiv (gamma:GL (Fin 2) ℝ) (hg:gamma∈modularImage)
    (tau:UpperHalfPlane) : (ModularWeierstrass318.curve tau).toAffine.Point ≃
      (ModularWeierstrass318.curve (gamma•tau)).toAffine.Point where
  toFun := pointMap gamma hg tau
  invFun := pointInverse gamma hg tau
  left_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
      simp [pointMap,pointInverse,WeierstrassCurve.Affine.Point.mk,denom_ne_zero gamma tau]
  right_inv P := by
    cases P with
    | zero => rfl
    | some x y h =>
      simp [pointMap,pointInverse,WeierstrassCurve.Affine.Point.mk,denom_ne_zero gamma tau,mul_div_cancel₀]

@[simp] theorem pointMap_zero (gamma:GL (Fin 2) ℝ) (hg:gamma∈modularImage)
    (tau:UpperHalfPlane) : pointMap gamma hg tau .zero=.zero := rfl

@[simp] theorem pointMap_some (gamma:GL (Fin 2) ℝ) (hg:gamma∈modularImage)
    (tau:UpperHalfPlane) (x y:ℂ) (h:(ModularWeierstrass318.curve tau).toAffine.Nonsingular x y) :
    pointMap gamma hg tau (.some x y h)=
    .mk ((equation_scale gamma hg tau x y).2 h.1) := rfl
/-- Every actual integral modular matrix transports the actual point sets. -/
@[expose] def slPointEquiv (gamma:SL(2,ℤ)) (tau:UpperHalfPlane) :
    (ModularWeierstrass318.curve tau).toAffine.Point ≃
    (ModularWeierstrass318.curve (((Matrix.SpecialLinearGroup.mapGL (R:=ℤ) ℝ) gamma) • tau)).toAffine.Point :=
  pointEquiv _ ⟨gamma,rfl⟩ tau
end ModularPointTransport318
#print axioms ModularPointTransport318.pointEquiv
