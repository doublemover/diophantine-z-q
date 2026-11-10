module
public import PELOriginalDescendedMetric318
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public section
noncomputable section
namespace PELOriginalLogMetricDerivatives318
open QuaternionicRealPeriod318 PELPeriodRiemannForm318
open PELOriginalPolarizationMetric318 PELOriginalMetricSmoothCoefficient318
variable (τ:ℂ) (hτ:0<τ.im)
@[expose] def imaginaryMap:ComplexVectors→L[ℝ]ComplexVectors:=
  Complex.I • ContinuousLinearMap.id ℝ ComplexVectors
@[expose] def logWeight (z:ComplexVectors):ℝ:=Real.log (weight τ hτ z)
lemma logWeight_formula (z:ComplexVectors):
    logWeight τ hτ z= -Real.pi*riemann τ hτ z (Complex.I • z):=by
  exact Real.log_exp _
@[expose] def firstDerivative (z:ComplexVectors):ComplexVectors→L[ℝ]ℝ:=
  (-2*Real.pi) • ((bilinear τ hτ z).comp imaginaryMap)

/-- First derivative of the log of the ACTUAL descended metric's
coefficient in every original local holomorphic frame. -/
lemma hasFDerivAt_logWeight (z:ComplexVectors):
    HasFDerivAt (logWeight τ hτ) (firstDerivative τ hτ z) z:=by
  have h:=((bilinear τ hτ).hasFDerivAt_of_bilinear
    (hasFDerivAt_id z) (imaginaryMap.hasFDerivAt (x:=z))).const_mul (-Real.pi)
  have he:(fun w:ComplexVectors=> -Real.pi*(bilinear τ hτ w (imaginaryMap w)))=
      logWeight τ hτ:=by
    funext w
    exact (logWeight_formula τ hτ w).symm
  rw [he] at h
  convert h using 1
  ext v
  change (-2*Real.pi)*riemann τ hτ z (Complex.I • v)=
    -Real.pi*(riemann τ hτ z (Complex.I • v)+riemann τ hτ v (Complex.I • z))
  rw [symmetric_real τ hτ z v]
  ring
lemma first_value (z v:ComplexVectors):
    fderiv ℝ (logWeight τ hτ) z v= -2*Real.pi*riemann τ hτ z (Complex.I • v):=by
  rw [(hasFDerivAt_logWeight τ hτ z).fderiv]
  rfl

/-- Actual second differential, obtained by differentiating the proved
first differential. It is independent of the base point, not postulated. -/
lemma second_value (z v w:ComplexVectors):
    fderiv ℝ (fun y:ComplexVectors=>fderiv ℝ (logWeight τ hτ) y v) z w=
      -2*Real.pi*riemann τ hτ w (Complex.I • v):=by
  have he:(fun y:ComplexVectors=>fderiv ℝ (logWeight τ hτ) y v)=
      fun y=> -2*Real.pi*(bilinear τ hτ).flip (Complex.I • v) y:=by
    funext y
    exact first_value τ hτ y v
  rw [he]
  rw [(((bilinear τ hτ).flip (Complex.I • v)).hasFDerivAt.const_mul (-2*Real.pi)).fderiv]
  change (-2*Real.pi)*riemann τ hτ w (Complex.I • v)=_
  ring
end PELOriginalLogMetricDerivatives318
