module
public import OriginalCasselsLiteralIsogenyPoint318
public import ActualTwoDescentFieldGeneralRootTranslation318
import all OriginalCasselsLiteralIsogenyPoint318
import all OriginalSelectedCasselsParity318
import all ActualTwoDescentEllipticModel318
import all ActualTwoDescentFieldGeneralRootTranslation318
public section

noncomputable section

namespace OriginalCasselsLiteralKernelTranslation318

open OriginalCasselsLiteralIsogenyPoint318 OriginalSelectedCasselsParity318
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldGeneralRootTranslation318

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

theorem actual_kernel_double (n : F) (hn : n≠0) :
    kernelPoint n hn+kernelPoint n hn=0 := by
  unfold kernelPoint point
  apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq
  rw [curve_negY,neg_zero]

private theorem actual_image_translation_affine (n x y : F) (hn : n ≠ 0) (hx : x ≠ 0)
    (he : y^2=x*(x-n)*(x+3*n)) :
    literalMap n hn (point n x y hn he+kernelPoint n hn)=
      literalMap n hn (point n x y hn he) := by
  let b := -3*n^2
  let X := b/x
  let Y := -b*y/x^2
  have hb : b ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hn)
  have hX : X ≠ 0 := div_ne_zero hb hx
  have hY : Y^2=X*(X-n)*(X+3*n) := by
    calc
      _ = (b^2/x^4)*y^2 := by dsimp [Y]; ring
      _ = _ := by rw [he]; dsimp [X,b]; field_simp [hx] <;> ring
  have hsum : point n x y hn he+kernelPoint n hn=point n X Y hn hY := by
    exact actual_add_root_point n x y 0 X Y hn
      (by simpa only [sub_zero] using hx) he (by simp) hY
      (by dsimp [X,b,rootDerivative]; ring)
      (by dsimp [Y,b,rootDerivative]; ring)
  rw [hsum,literal_affine n hn X Y hX hY,literal_affine n hn x y hx he]
  unfold imagePoint targetPoint
  congr 1
  · dsimp [X,b]; field_simp [hx,hn] <;> ring
  · dsimp [X,Y,b]; field_simp [hx,hn] <;> ring

/-- Native compatibility for the omitted root, including both
exceptional input points and every true affine preimage. -/
theorem actual_image_translation (n : F) (hn : n ≠ 0) (P : Point n) :
    literalMap n hn (P+kernelPoint n hn)=literalMap n hn P := by
  cases P with
  | zero =>
    change literalMap n hn ((0 : Point n) + kernelPoint n hn) = literalMap n hn 0
    rw [zero_add,literal_kernel_point,literal_zero]
  | some x y hxy =>
    have he := (curve_equation n x y).mp hxy.left
    by_cases hx : x=0
    · subst x
      have hy : y=0 := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (by simpa using he)
      subst y
      change literalMap n hn (kernelPoint n hn+kernelPoint n hn)=literalMap n hn (kernelPoint n hn)
      rw [actual_kernel_double,literal_zero,literal_kernel_point]
    · exact actual_image_translation_affine n x y hn hx he

end OriginalCasselsLiteralKernelTranslation318

#print axioms OriginalCasselsLiteralKernelTranslation318.actual_image_translation
