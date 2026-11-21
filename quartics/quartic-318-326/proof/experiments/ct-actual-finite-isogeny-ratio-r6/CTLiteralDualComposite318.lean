module
public import CTDegreeTwoCompositeCoordinates318
public import CTLiteralDualFiberTargetPoints318
public import OriginalCasselsLiteralIsogenyPoint318
import all CTLiteralDualFiberTargetPoints318
import all OriginalCasselsLiteralIsogenyPoint318
import all ActualTwoDescentEllipticModel318
import all OriginalSelectedCasselsParity318
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
public section
noncomputable section

namespace CTLiteralDualComposite318

open CTDegreeTwoCompositeCoordinates318 CTLiteralDualFiberTargetPoints318
open CTLiteralDualFiberCoordinates318 OriginalCasselsLiteralIsogenyPoint318
open ActualTwoDescentEllipticModel318 OriginalSelectedCasselsLocalArithmetic318
open OriginalSelectedCasselsParity318 WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

private theorem y_ne_negY {n x y : K} (hy : y≠0) : y ≠ (curve n).toAffine.negY x y := by
  rw [curve_negY]
  intro he
  have h : (2:K)*y=0 := calc
    _=y+y := two_mul _
    _= -y+y := congrArg (fun a : K => a+y) he
    _=0 := neg_add_cancel _
  exact mul_ne_zero (by norm_num) hy h

private theorem x_add_term (n x y : K) (hx : x≠0)
    (he : y^2=x*(x-n)*(x+3*n)) :
    x+2*n-3*n^2/x=y^2/x^2 := by
  rw [he]
  field_simp [hx] <;> ring

private theorem ordinary_slopes {n x y : K} (hy : y≠0) :
    (curve n).toAffine.slope x x y y=(3*x^2+2*(2*n)*x+(-3*n^2))/(2*y) := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl (y_ne_negY (n:=n) (x:=x) hy)]
  rw [curve_negY]
  simp only [curve,zero_mul,add_zero,zero_add,sub_zero]
  congr 1 <;> ring

/-- The actual signed reverse∘forward is [2] on the original point
group over every characteristic-zero field. Exceptional points are
handled as points, without division by zero or a recovery oracle. -/
theorem dual_literal_add_self (n : K) (hn : n≠0) (P : Point n) :
    dualPoint n hn (literalMap n hn P)=P+P := by
  cases P with
  | zero =>
    change dualPoint n hn (literalMap n hn (0 : Point n))=(0 : Point n)+0
    rw [literal_zero,dual_zero,zero_add]
  | some x y hz =>
    have he := (curve_equation n x y).mp hz.left
    change dualPoint n hn (literalMap n hn (point n x y hn he))=
      point n x y hn he+point n x y hn he
    by_cases hx : x=0
    · subst x
      have hy : y=0 := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (by simpa using he)
      subst y
      rw [show point n 0 0 hn he=kernelPoint n hn from rfl,literal_kernel_point,dual_zero]
      unfold kernelPoint point
      exact (WeierstrassCurve.Affine.Point.add_self_of_Y_eq (by rw [curve_negY,neg_zero])).symm
    rw [literal_affine n hn x y hx he]
    let S := x+2*n-3*n^2/x
    let T := y+3*n^2*y/x^2
    have hEq := affine_isogeny_chart n x y hx he
    change dualPoint n hn (targetPoint n S T hn hEq)=point n x y hn he+point n x y hn he
    by_cases hy : y=0
    · subst y
      have hS : S=0 := by rw [show S=0^2/x^2 from x_add_term n x 0 hx he]; simp
      have hT : T=0 := by simp [T]
      have hQ : targetPoint n S T hn hEq=targetKernel n hn := by
        unfold targetKernel targetPoint
        congr 1
        · exact hS
        · exact hT
      rw [hQ,dual_target_kernel]
      unfold point
      exact (WeierstrassCurve.Affine.Point.add_self_of_Y_eq (by rw [curve_negY,neg_zero])).symm
    have hs : S≠0 := by
      rw [show S=y^2/x^2 from x_add_term n x y hx he]
      exact div_ne_zero (pow_ne_zero 2 hy) (pow_ne_zero 2 hx)
    rw [dual_affine n S T hn hs hEq]
    have hE : y^2=x*(x^2+(2*n)*x+(-3*n^2)) := by linear_combination he
    have hXY := signed_affine_composition (2*n) (-3*n^2) x y hx hy hE
    dsimp only at hXY
    have hS' : x+2*n+(-3*n^2)/x=S := by dsimp [S]; ring
    have hT' : y-(-3*n^2)*y/x^2=T := by dsimp [T]; ring
    have hD : (2*n)^2-4*(-3*n^2)=16*n^2 := by ring
    rw [hS',hT',hD] at hXY
    have hne := y_ne_negY (n:=n) (x:=x) hy
    unfold point
    rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne]
    congr 1
    · rw [WeierstrassCurve.Affine.addX,ordinary_slopes hy]
      change backX n S=_
      simp only [curve,zero_mul,add_zero]
      unfold backX
      calc
        (S-4*n+16*n^2/S)/4=(S-2*(2*n)+16*n^2/S)/4 := by ring
        _=_ := hXY.1.trans (by ring)
    · rw [WeierstrassCurve.Affine.addY,curve_negY,WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.addX,ordinary_slopes hy]
      change backY n S T=_
      simp only [curve,zero_mul,add_zero]
      unfold backY
      exact hXY.2.trans (by ring)

/-- A chosen root of the genuine target abscissa supplies a lift
for the actual already-green forward point formula. -/
theorem literal_affine_fiber (n s t r : K) (hn : n≠0) (hs : s≠0) (hr : r^2=s)
    (he : t^2=s*(s^2-4*n*s+16*n^2)) :
    ∃ P : Point n, literalMap n hn P=targetPoint n s t hn he := by
  have hB : -3*n^2≠0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hn)
  have he' : t^2=s*(s^2-2*(2*n)*s+((2*n)^2-4*(-3*n^2))) := by linear_combination he
  obtain ⟨hx,hY,hX,hT⟩ := signed_forward_fiber (2*n) (-3*n^2) s t r hB hs hr he'
  let x := (s-2*n+t/r)/2
  let y := r*x
  change x≠0 at hx
  change y^2=x*(x^2+2*n*x+(-3*n^2)) at hY
  have hOrig : y^2=x*(x-n)*(x+3*n) := by linear_combination hY
  refine ⟨point n x y hn hOrig,?_⟩
  rw [literal_affine n hn x y hx hOrig]
  unfold imagePoint targetPoint
  congr 1
  · change x+2*n+(-3*n^2)/x=s at hX
    calc x+2*n-3*n^2/x=x+2*n+(-3*n^2)/x := by ring
         _=s := hX
  · change y-(-3*n^2)*y/x^2=t at hT
    calc y+3*n^2*y/x^2=y-(-3*n^2)*y/x^2 := by ring
         _=t := hT

theorem literal_target_kernel_fiber (n : K) (hn : n≠0) :
    literalMap n hn (point n n 0 hn (by simp))=targetKernel n hn := by
  rw [literal_affine n hn n 0 hn (by simp)]
  unfold imagePoint targetKernel targetPoint
  congr 1
  · field_simp [hn] <;> ring
  · ring

end CTLiteralDualComposite318

#print axioms CTLiteralDualComposite318.dual_literal_add_self
#print axioms CTLiteralDualComposite318.literal_affine_fiber
#print axioms CTLiteralDualComposite318.literal_target_kernel_fiber
