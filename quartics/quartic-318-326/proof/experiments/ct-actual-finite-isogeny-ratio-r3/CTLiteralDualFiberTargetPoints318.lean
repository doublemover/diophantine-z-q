module
public import CTLiteralDualFiberCoordinates318
import all CTLiteralDualFiberCoordinates318
public import OriginalSelectedCasselsParity318
import all OriginalSelectedCasselsParity318
import all ActualTwoDescentEllipticModel318
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
public section

noncomputable section
namespace CTLiteralDualFiberTargetPoints318

open ActualTwoDescentEllipticModel318 OriginalSelectedCasselsParity318
open CTLiteralDualFiberCoordinates318
open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

private theorem target_curve_equation (n s t : K) (h : (targetModel n).toAffine.Nonsingular s t) :
    t^2=s*(s^2-4*n*s+16*n^2) := by
  have he := h.left
  rw [WeierstrassCurve.Affine.equation_iff] at he
  simp only [targetModel,zero_mul,add_zero,zero_add] at he
  linear_combination he

/-- Literal reverse point map. Its point-set fibers and their changes
of root are proved here; additivity and composition [2] are separate. -/
def dualPoint (n : K) (hn : n≠0) : TargetPoint n → Point n
  | .zero => .zero
  | .some s t h =>
    if hs : s=0 then .zero else
      point n (backX n s) (backY n s t) hn
        (back_affine_equation n s t hs (target_curve_equation n s t h))

def targetKernel (n : K) (hn : n≠0) : TargetPoint n := targetPoint n 0 0 hn (by simp)

theorem dual_zero (n : K) (hn : n≠0) : dualPoint n hn 0=0 := rfl

theorem dual_target_kernel (n : K) (hn : n≠0) :
    dualPoint n hn (targetKernel n hn)=0 := by
  simp [targetKernel,targetPoint,dualPoint]

theorem dual_affine (n s t : K) (hn : n≠0) (hs : s≠0)
    (h : t^2=s*(s^2-4*n*s+16*n^2)) :
    dualPoint n hn (targetPoint n s t hn h) =
      point n (backX n s) (backY n s t) hn (back_affine_equation n s t hs h) := by
  simp [targetPoint,dualPoint,hs]

def fiberPoint {n x y : K} (hn : n≠0) (P : Fiber n x y) : TargetPoint n :=
  targetPoint n P.s P.t hn P.equation

theorem dual_fiber_point {n x y : K} (hn : n≠0) (P : Fiber n x y)
    (he : y^2=x*(x-n)*(x+3*n)) :
    dualPoint n hn (fiberPoint hn P)=point n x y hn he := by
  unfold fiberPoint
  rw [dual_affine n P.s P.t hn P.s_ne P.equation]
  unfold point
  congr 1
  · exact P.image_x
  · exact P.image_y

private theorem target_slope_kernel (n s t : K) (hs : s≠0) :
    (targetModel n).toAffine.slope s 0 t 0=t/s := by
  rw [WeierstrassCurve.Affine.slope_of_X_ne hs]
  congr 1 <;> ring

private theorem target_addX_kernel (n s t : K) (hs : s≠0)
    (he : t^2=s*(s^2-4*n*s+16*n^2)) :
    (targetModel n).toAffine.addX s 0 ((targetModel n).toAffine.slope s 0 t 0)=16*n^2/s := by
  rw [target_slope_kernel n s t hs]
  dsimp [WeierstrassCurve.Affine.addX,targetModel]
  field_simp [hs] <;> linear_combination he

private theorem target_addY_kernel (n s t : K) (hs : s≠0)
    (he : t^2=s*(s^2-4*n*s+16*n^2)) :
    (targetModel n).toAffine.addY s 0 t ((targetModel n).toAffine.slope s 0 t 0)=
      -(16*n^2)*t/s^2 := by
  have hNeg (x y : K) : (targetModel n).toAffine.negY x y= -y := by simp [negY,targetModel]
  rw [WeierstrassCurve.Affine.addY,hNeg,WeierstrassCurve.Affine.negAddY,
    target_addX_kernel n s t hs he,target_slope_kernel n s t hs]
  field_simp [hs] <;> ring

theorem target_kernel_translate (n s t X Y : K) (hn : n≠0) (hs : s≠0)
    (he : t^2=s*(s^2-4*n*s+16*n^2))
    (hXY : Y^2=X*(X^2-4*n*X+16*n^2))
    (hX : X=16*n^2/s) (hY : Y= -(16*n^2)*t/s^2) :
    targetPoint n s t hn he+targetKernel n hn=targetPoint n X Y hn hXY := by
  unfold targetKernel targetPoint
  rw [WeierstrassCurve.Affine.Point.add_of_X_ne hs]
  congr 1
  · exact (target_addX_kernel n s t hs he).trans hX.symm
  · exact (target_addY_kernel n s t hs he).trans hY.symm

theorem affine_switch_is_target_kernel (n x y r : K) (hn : n≠0) (hx : x≠0) (hr : r^2=x)
    (he : y^2=x*(x-n)*(x+3*n)) :
    fiberPoint hn (affineFiber n x y (-r) hn hx (by rw [neg_sq,hr]) he) =
      fiberPoint hn (affineFiber n x y r hn hx hr he)+targetKernel n hn := by
  let A := affineFiber n x y r hn hx hr he
  let B := affineFiber n x y (-r) hn hx (by rw [neg_sq,hr]) he
  have h := affine_sign_switch n x y r hn hx hr he
  change fiberPoint hn B=fiberPoint hn A+targetKernel n hn
  unfold fiberPoint
  exact (target_kernel_translate n A.s A.t B.s B.t hn A.s_ne A.equation B.equation h.1 h.2).symm

theorem kernel_switch_is_target_kernel (n r : K) (hn : n≠0) (hr : r^2= -3*n^2) :
    fiberPoint hn (kernelFiber n (-r) hn (by rw [neg_sq,hr])) =
      fiberPoint hn (kernelFiber n r hn hr)+targetKernel n hn := by
  let A := kernelFiber n r hn hr
  let B := kernelFiber n (-r) hn (by rw [neg_sq,hr])
  change fiberPoint hn B=fiberPoint hn A+targetKernel n hn
  unfold fiberPoint
  refine (target_kernel_translate n A.s A.t B.s B.t hn A.s_ne A.equation B.equation
    (kernel_sign_switch n r hn hr) ?_).symm
  change (0:K)= -(16*n^2)*0/A.s^2
  simp

end CTLiteralDualFiberTargetPoints318

#print axioms CTLiteralDualFiberTargetPoints318.dual_fiber_point
#print axioms CTLiteralDualFiberTargetPoints318.affine_switch_is_target_kernel
#print axioms CTLiteralDualFiberTargetPoints318.kernel_switch_is_target_kernel
