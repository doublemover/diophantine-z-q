module
public import ActualMillerLineFactor318
public import ActualMillerNormalizedFunction318
public import Mathlib.Algebra.Polynomial.Bivariate
import all ActualMillerNormalizedFunction318
import all ActualTwoDescentAffineChartCoordinates318
import all ActualTwoDescentOriginalFunctionFieldTheta318
public section
noncomputable section

namespace ActualMillerRegularEvaluation318

open Polynomial
open ActualTwoDescentEllipticModel318 ActualTwoDescentAffineChartCoordinates318
open ActualTwoDescentOriginalFunctionFieldTheta318
open ActualMillerLineFactor318 ActualMillerInfinityNormalization318

variable {K : Type*} [Field K] [CharZero K]

/-- The exact pinned AdjoinRoot evaluation of the native affine chart. -/
abbrev affineEval (n u v : K) (hR : (curve n).toAffine.Equation u v) :
    AffineChart n →+* K :=
  AdjoinRoot.evalEval (p := (curve n).toAffine.polynomial) (x := u) (y := v) hR

@[simp] theorem affineEval_x (n u v : K) (hR : (curve n).toAffine.Equation u v) :
    affineEval n u v hR (affineX n) = u := by
  change AdjoinRoot.evalEval hR (AdjoinRoot.mk _ (C X)) = u
  rw [AdjoinRoot.evalEval_mk, evalEval_C, eval_X]

@[simp] theorem affineEval_y (n u v : K) (hR : (curve n).toAffine.Equation u v) :
    affineEval n u v hR (affineY n) = v := by
  change AdjoinRoot.evalEval hR (AdjoinRoot.mk _ X) = v
  rw [AdjoinRoot.evalEval_mk, evalEval_X]

@[simp] theorem affineEval_const (n u v a : K) (hR : (curve n).toAffine.Equation u v) :
    affineEval n u v hR (affineCoefficient n a) = a := by
  change AdjoinRoot.evalEval hR (AdjoinRoot.mk _ (C (C a))) = a
  rw [AdjoinRoot.evalEval_mk, evalEval_C, eval_C]

/-- The signed affine numerator and vertical denominator, chosen to agree
with the exact principal ideal generators in pinned Mathlib. -/
def lineNumerator (n x y a : K) : AffineChart n :=
  -(WeierstrassCurve.Affine.CoordinateRing.YClass (curve n).toAffine
    (WeierstrassCurve.Affine.linePolynomial x y a))

def vertical (n z : K) : AffineChart n :=
  WeierstrassCurve.Affine.CoordinateRing.XClass (curve n).toAffine z

theorem lineNumerator_coordinates (n x y a : K) :
    lineNumerator n x y a =
      affineCoefficient n a * (affineX n - affineCoefficient n x) +
        affineCoefficient n y - affineY n := by
  simp only [lineNumerator, WeierstrassCurve.Affine.CoordinateRing.YClass,
    WeierstrassCurve.Affine.linePolynomial, map_sub, map_add, map_mul, neg_sub] <;> rfl

theorem vertical_coordinates (n z : K) :
    vertical n z = affineX n - affineCoefficient n z := by
  simp only [vertical, WeierstrassCurve.Affine.CoordinateRing.XClass, map_sub] <;> rfl

@[simp] theorem affineEval_lineNumerator (n u v x y a : K)
    (hR : (curve n).toAffine.Equation u v) :
    affineEval n u v hR (lineNumerator n x y a) = a * (u - x) + y - v := by
  simp only [lineNumerator_coordinates, map_sub, map_add, map_mul,
    affineEval_const, affineEval_x, affineEval_y]

@[simp] theorem affineEval_vertical (n u v z : K) (hR : (curve n).toAffine.Equation u v) :
    affineEval n u v hR (vertical n z) = u - z := by
  simp only [vertical_coordinates, map_sub, affineEval_x, affineEval_const]

abbrev LineOpen (n z : K) := Localization.Away (vertical n z)
abbrev openBase (n z : K) : AffineChart n →+* LineOpen n z := algebraMap _ _
abbrev fractionalBase (n : K) : AffineChart n →+* OriginalFunctionField n := algebraMap _ _

def regularLineSection (n x y a z : K) : LineOpen n z :=
  openBase n z (lineNumerator n x y a) * IsLocalization.Away.invSelf (vertical n z)

def evaluateOpen (n u v z : K) (hR : (curve n).toAffine.Equation u v) (hz : u ≠ z) :
    LineOpen n z →+* K :=
  IsLocalization.Away.lift (vertical n z) (g := affineEval n u v hR)
    (by rw [affineEval_vertical]; exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hz))

def openIntoFunction (n z : K) : LineOpen n z →+* OriginalFunctionField n :=
  IsLocalization.Away.lift (vertical n z) (g := fractionalBase n)
    (isUnit_iff_ne_zero.mpr (actual_root_function_nonzero n z))

private theorem section_image {M : Type*} [Field M] (n x y a z : K)
    (g : LineOpen n z →+* M) (h : g (openBase n z (vertical n z)) ≠ 0) :
    g (regularLineSection n x y a z) =
      g (openBase n z (lineNumerator n x y a)) / g (openBase n z (vertical n z)) := by
  have hi : g (IsLocalization.Away.invSelf (S := LineOpen n z) (vertical n z)) =
      (g (openBase n z (vertical n z)))⁻¹ := by
    apply actual_inverse_unique (g (openBase n z (vertical n z)))
    · have h' := congrArg g (IsLocalization.Away.mul_invSelf (S := LineOpen n z) (vertical n z))
      simpa only [map_mul, map_one] using h'
    · exact mul_inv_cancel₀ h
  rw [regularLineSection, map_mul, hi, div_eq_mul_inv]

theorem evaluate_regular_section (n u v x y a z : K)
    (hR : (curve n).toAffine.Equation u v) (hz : u ≠ z) :
    evaluateOpen n u v z hR hz (regularLineSection n x y a z) =
      (a * (u - x) + y - v) / (u - z) := by
  have hbase (r : AffineChart n) :
      evaluateOpen n u v z hR hz (openBase n z r) = affineEval n u v hR r :=
    IsLocalization.Away.lift_eq _ _ _
  have hD : evaluateOpen n u v z hR hz (openBase n z (vertical n z)) ≠ 0 := by
    rw [hbase, affineEval_vertical]
    exact sub_ne_zero.mpr hz
  simp only [section_image n x y a z _ hD, hbase, affineEval_lineNumerator, affineEval_vertical]

theorem regular_section_is_same_function (n x y a z : K) :
    openIntoFunction n z (regularLineSection n x y a z) = nonverticalFunction n x y a z := by
  have hbase (r : AffineChart n) :
      openIntoFunction n z (openBase n z r) = fractionalBase n r :=
    IsLocalization.Away.lift_eq _ _ _
  have hD : openIntoFunction n z (openBase n z (vertical n z)) ≠ 0 := by
    rw [hbase]
    exact actual_root_function_nonzero n z
  simp only [section_image n x y a z _ hD, hbase, lineNumerator_coordinates, vertical_coordinates,
    nonverticalFunction, map_add, map_sub, map_mul] <;> rfl

variable [DecidableEq K]

/-- Consumer for the existing noncollision test: not a separate point
formula, but literal evaluation of the section of the actual principal open. -/
theorem affineFactor_is_regular_section_value (n x₁ y₁ x₂ y₂ u v : K)
    (h₁ : (curve n).toAffine.Equation x₁ y₁) (h₂ : (curve n).toAffine.Equation x₂ y₂)
    (hR : (curve n).toAffine.Equation u v) (hInv : ¬(x₁ = x₂ ∧ y₁ = -y₂))
    (h₁u : u ≠ x₁) (h₂u : u ≠ x₂)
    (hz : u ≠ (curve n).toAffine.addX x₁ x₂ ((curve n).toAffine.slope x₁ x₂ y₁ y₂)) :
    let a := (curve n).toAffine.slope x₁ x₂ y₁ y₂
    let z := (curve n).toAffine.addX x₁ x₂ a
    affineFactor n x₁ y₁ x₂ y₂ u v =
      some (evaluateOpen n u v z hR hz (regularLineSection n x₁ y₁ a z)) := by
  dsimp only
  rw [evaluate_regular_section]
  exact affineFactor_noncollision n x₁ y₁ x₂ y₂ u v h₁ h₂ hR hInv h₁u h₂u hz

end ActualMillerRegularEvaluation318
