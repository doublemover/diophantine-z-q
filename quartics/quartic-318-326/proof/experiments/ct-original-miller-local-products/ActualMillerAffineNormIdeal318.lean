module
public import ActualMillerRegularEvaluation318
public import Mathlib.Tactic.Ring
import all ActualMillerRegularEvaluation318
import all ActualTwoDescentAffineChartCoordinates318
public section
noncomputable section

namespace ActualMillerAffineNormIdeal318

open Polynomial
open ActualTwoDescentEllipticModel318 ActualTwoDescentAffineChartCoordinates318
open ActualMillerRegularEvaluation318
open WeierstrassCurve.Affine.CoordinateRing
open Ideal (span_singleton_neg)

variable {K : Type*} [Field K] [CharZero K]

private theorem lineNumerator_basis (n x y a : K) :
    lineNumerator n x y a =
      (WeierstrassCurve.Affine.linePolynomial x y a) • (1 : AffineChart n) +
        (-1 : Polynomial K) • affineY n := by
  rw [lineNumerator, YClass, map_sub, neg_sub, neg_smul, one_smul, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one,
    sub_eq_add_neg] <;> rfl

private theorem vertical_basis (n z : K) :
    vertical n z =
      (X - C z) • (1 : AffineChart n) + (0 : Polynomial K) • affineY n := by
  rw [zero_smul, add_zero, WeierstrassCurve.Affine.CoordinateRing.smul, mul_one] <;> rfl

/-- Exact quadratic norm of the chosen signed affine numerator.
This is the native finite-rank coordinate-ring norm over K[X]. -/
theorem norm_lineNumerator (n x y a : K) :
    Algebra.norm (Polynomial K) (lineNumerator n x y a) =
      (curve n).toAffine.addPolynomial x y a := by
  rw [lineNumerator_basis, norm_smul_basis]
  simp only [WeierstrassCurve.Affine.addPolynomial, WeierstrassCurve.Affine.polynomial,
    eval_X, eval_C, eval_add, eval_mul, eval_sub, eval_pow]
  ring

theorem norm_vertical (n z : K) :
    Algebra.norm (Polynomial K) (vertical n z) = (X - C z)^2 := by
  rw [vertical_basis, norm_smul_basis]
  ring

variable [DecidableEq K]

/-- Exact numerator and denominator norms for the SAME regular
nonvertical section, before rational-function cancellation. -/
theorem norm_secant_factors (n x₁ y₁ x₂ y₂ : K)
    (h₁ : (curve n).toAffine.Equation x₁ y₁)
    (h₂ : (curve n).toAffine.Equation x₂ y₂)
    (hInv : ¬(x₁ = x₂ ∧ y₁ = (curve n).toAffine.negY x₂ y₂)) :
    let a := (curve n).toAffine.slope x₁ x₂ y₁ y₂
    let z := (curve n).toAffine.addX x₁ x₂ a
    Algebra.norm (Polynomial K) (lineNumerator n x₁ y₁ a) =
      -((X - C x₁) * (X - C x₂) * (X - C z)) ∧
    Algebra.norm (Polynomial K) (vertical n z) = (X - C z)^2 := by
  dsimp only
  constructor
  · rw [norm_lineNumerator]
    exact (curve n).toAffine.addPolynomial_slope h₁ h₂ hInv
  · exact norm_vertical _ _

/-- Exact cleared affine ideal equality for the same section. This is
not a projective divisor comparison or a reciprocity theorem. -/
theorem affine_line_ideal_identity (n x₁ y₁ x₂ y₂ : K)
    (h₁ : (curve n).toAffine.Equation x₁ y₁)
    (h₂ : (curve n).toAffine.Equation x₂ y₂)
    (hInv : ¬(x₁ = x₂ ∧ y₁ = (curve n).toAffine.negY x₂ y₂)) :
    let W := (curve n).toAffine
    let a := W.slope x₁ x₂ y₁ y₂
    let z := W.addX x₁ x₂ a
    Ideal.span ({vertical n z} : Set (AffineChart n)) *
      (XYIdeal W x₁ (C y₁) * XYIdeal W x₂ (C y₂)) =
      Ideal.span ({lineNumerator n x₁ y₁ a} : Set (AffineChart n)) *
        XYIdeal W z (C (W.addY x₁ x₂ y₁ a)) := by
  simpa only [XIdeal, YIdeal, vertical, lineNumerator, span_singleton_neg] using
    (XYIdeal_mul_XYIdeal h₁ h₂ hInv)

end ActualMillerAffineNormIdeal318
