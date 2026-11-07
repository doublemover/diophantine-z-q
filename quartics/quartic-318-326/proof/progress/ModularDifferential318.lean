module
public import ModularPointTransport318
public import Mathlib.RingTheory.Derivation.Basic
public section
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups
namespace ModularDifferential318
set_option maxHeartbeats 0

/-- Genuine derivations of a complex function field annihilate the modular
coordinate-change constant, hence dx'/(2y') has weight minus one. -/
theorem differential_scale {K:Type*} [Field K] [Algebra ℂ K]
    (D:Derivation ℂ K K) (u:ℂ) (hu:u≠0) (x y:K) :
    D ((algebraMap ℂ K u)^2*x)/(2*((algebraMap ℂ K u)^3*y))=
      (algebraMap ℂ K u)⁻¹*(D x/(2*y)) := by
  have hv : algebraMap ℂ K u ≠ 0 := (map_ne_zero (algebraMap ℂ K)).2 hu
  have hd : D ((algebraMap ℂ K u)^2*x)=(algebraMap ℂ K u)^2*D x := by
    have hpow : (algebraMap ℂ K u)^2 = algebraMap ℂ K (u^2) := by simp
    rw [hpow,D.leibniz,D.map_algebraMap]
    simp
  rw [hd]
  by_cases hy:y=0
  · simp [hy]
  · field_simp

/-- The old-to-new point map is x'=j²x,y'=j³y, so its pullback on the
invariant differential is j⁻¹, where j=c*tau+d. -/
theorem modular_differential_weight {K:Type*} [Field K] [Algebra ℂ K]
    (D:Derivation ℂ K K) (gamma:GL (Fin 2) ℝ) (tau:UpperHalfPlane) (x y:K) :
    D ((algebraMap ℂ K (denom gamma tau))^2*x)/
      (2*((algebraMap ℂ K (denom gamma tau))^3*y))=
      (algebraMap ℂ K (denom gamma tau))⁻¹*(D x/(2*y)) :=
  differential_scale D _ (denom_ne_zero gamma tau) x y

/-- Squaring the differential gives the precise weight minus two. -/
theorem modular_quadratic_differential_weight {K:Type*} [Field K] [Algebra ℂ K]
    (D:Derivation ℂ K K) (gamma:GL (Fin 2) ℝ) (tau:UpperHalfPlane) (x y:K) :
    (D ((algebraMap ℂ K (denom gamma tau))^2*x)/
      (2*((algebraMap ℂ K (denom gamma tau))^3*y)))^2=
      ((algebraMap ℂ K (denom gamma tau))⁻¹)^2*(D x/(2*y))^2 := by
  rw [modular_differential_weight,mul_pow]
/-- This denominator is the actual Y-partial derivative of the curve equation. -/
theorem curve_polynomialY (tau:UpperHalfPlane) (x y:ℂ) :
    (ModularWeierstrass318.curve tau).toAffine.polynomialY.evalEval x y=2*y := by
  simp [WeierstrassCurve.Affine.evalEval_polynomialY,ModularWeierstrass318.curve,
    NormalizedWeierstrass318.model]

/-- Actual analytic coordinate differentiation gives the same pullback weight
on every affine chart where the standard invariant-differential denominator is nonzero. -/
theorem analytic_differential_pullback (gamma:GL (Fin 2) ℝ) (tau:UpperHalfPlane)
    (x:ℂ→ℂ) (z dx y:ℂ) (hx:HasDerivAt x dx z) (hy:y≠0) :
    deriv (fun t=>denom gamma tau^2*x t) z /
      (ModularWeierstrass318.curve (gamma•tau)).toAffine.polynomialY.evalEval
        (denom gamma tau^2*x z) (denom gamma tau^3*y)=
    (denom gamma tau)⁻¹*(dx/
      (ModularWeierstrass318.curve tau).toAffine.polynomialY.evalEval (x z) y) := by
  rw [curve_polynomialY,curve_polynomialY,(hx.const_mul (denom gamma tau^2)).deriv]
  have hu := denom_ne_zero gamma tau
  field_simp

end ModularDifferential318
#print axioms ModularDifferential318.modular_differential_weight
