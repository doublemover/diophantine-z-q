module
public import OriginalCasselsLiteralKernelTranslation318
import all OriginalCasselsLiteralIsogenyPoint318
import all OriginalSelectedCasselsParity318
import all ActualTwoDescentEllipticModel318
public section

noncomputable section

namespace OriginalCasselsLiteralIsogenyExceptional318

open OriginalCasselsLiteralIsogenyPoint318 OriginalCasselsLiteralKernelTranslation318
open ActualTwoDescentEllipticModel318 OriginalSelectedCasselsParity318

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

theorem target_negY (n x y : F) : (targetModel n).toAffine.negY x y = -y := by
  simp [WeierstrassCurve.Affine.negY,targetModel]

theorem actual_point_neg (n x y : F) (hn : n ≠ 0) (he : y^2=x*(x-n)*(x+3*n)) :
    -point n x y hn he =
      point n x (-y) hn (by simpa only [neg_sq] using he) := by
  unfold point
  simp only [WeierstrassCurve.Affine.Point.neg_some,curve_negY]

theorem actual_image_neg (n x y : F) (hn : n ≠ 0) (hx : x ≠ 0)
    (he : y^2=x*(x-n)*(x+3*n)) :
    imagePoint n x (-y) hn hx (by simpa only [neg_sq] using he) =
      -imagePoint n x y hn hx he := by
  unfold imagePoint targetPoint
  simp only [WeierstrassCurve.Affine.Point.neg_some,target_negY]
  congr 1
  ring

/-- This is a statement about the fixed map and the actual point-group
negation, not an application of additivity. -/
theorem actual_literal_neg (n : F) (hn : n ≠ 0) (P : Point n) :
    literalMap n hn (-P) = -literalMap n hn P := by
  cases P with
  | zero =>
    change literalMap n hn (-(0 : Point n)) = -literalMap n hn 0
    rw [neg_zero,literal_zero,neg_zero]
  | some x y h =>
    have he := (curve_equation n x y).mp h.left
    change literalMap n hn (-point n x y hn he) = -literalMap n hn (point n x y hn he)
    by_cases hx : x = 0
    · subst x
      have hy : y = 0 :=
        (pow_eq_zero_iff (by decide : (2:ℕ) ≠ 0)).mp (by simpa using he)
      subst y
      change literalMap n hn (-(kernelPoint n hn)) = -literalMap n hn (kernelPoint n hn)
      have hneg : -(kernelPoint n hn) = kernelPoint n hn :=
        neg_eq_of_add_eq_zero_right (actual_kernel_double n hn)
      rw [hneg,literal_kernel_point,neg_zero]
    · rw [actual_point_neg,literal_affine n hn x (-y) hx,literal_affine n hn x y hx]
      exact actual_image_neg n x y hn hx he

theorem actual_add_right_zero (n : F) (hn : n ≠ 0) (P : Point n) :
    literalMap n hn (P+0) = literalMap n hn P+literalMap n hn 0 := by
  rw [add_zero,literal_zero,add_zero]

theorem actual_add_left_zero (n : F) (hn : n ≠ 0) (P : Point n) :
    literalMap n hn (0+P) = literalMap n hn 0+literalMap n hn P := by
  rw [zero_add,literal_zero,zero_add]

theorem actual_add_right_kernel (n : F) (hn : n ≠ 0) (P : Point n) :
    literalMap n hn (P+kernelPoint n hn) =
      literalMap n hn P+literalMap n hn (kernelPoint n hn) := by
  rw [actual_image_translation,literal_kernel_point,add_zero]

theorem actual_add_left_kernel (n : F) (hn : n ≠ 0) (P : Point n) :
    literalMap n hn (kernelPoint n hn+P) =
      literalMap n hn (kernelPoint n hn)+literalMap n hn P := by
  simpa only [add_comm] using actual_add_right_kernel n hn P

theorem actual_add_vertical (n : F) (hn : n ≠ 0) (P : Point n) :
    literalMap n hn (P+(-P)) = literalMap n hn P+literalMap n hn (-P) := by
  rw [add_neg_cancel,literal_zero,actual_literal_neg,add_neg_cancel]

/-- A secant with zero intercept meets the zero root. This rule uses that
exact sum, not an assumed affine-map homomorphism. -/
theorem actual_add_sum_kernel (n : F) (hn : n ≠ 0) (P Q : Point n)
    (h : P+Q = kernelPoint n hn) :
    literalMap n hn (P+Q) = literalMap n hn P+literalMap n hn Q := by
  have hQ : Q = (-P)+kernelPoint n hn := by
    rw [←h,←add_assoc,neg_add_cancel,zero_add]
  have hQ' : literalMap n hn Q = -literalMap n hn P := by
    rw [hQ,actual_image_translation,actual_literal_neg]
  rw [h,literal_kernel_point,hQ',add_neg_cancel]

end OriginalCasselsLiteralIsogenyExceptional318

#print axioms OriginalCasselsLiteralIsogenyExceptional318.actual_literal_neg
#print axioms OriginalCasselsLiteralIsogenyExceptional318.actual_add_sum_kernel
