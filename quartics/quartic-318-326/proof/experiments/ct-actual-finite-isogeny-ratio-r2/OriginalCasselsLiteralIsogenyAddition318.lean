module
public import OriginalCasselsLiteralIsogenyTangent318
public import Mathlib.Tactic.Abel
import all ActualTwoDescentEllipticModel318
import all ActualTwoDescentFieldGeneralRootTranslation318
import all OriginalCasselsLiteralIsogenyPoint318
public section

noncomputable section

namespace OriginalCasselsLiteralIsogenyAddition318

open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldGeneralRootTranslation318
open OriginalCasselsLiteralIsogenyPoint318 OriginalCasselsLiteralKernelTranslation318
open OriginalCasselsLiteralIsogenyExceptional318 OriginalCasselsLiteralIsogenySecant318
open OriginalCasselsLiteralIsogenyTangent318 WeierstrassCurve.Affine

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

private theorem kernel_neg (n : F) (hn : n ≠ 0) :
    -kernelPoint n hn = kernelPoint n hn := by
  unfold kernelPoint
  rw [actual_point_neg]
  unfold point
  rw [Point.some.injEq]
  exact ⟨rfl, neg_zero⟩

private theorem affine_zero_x (n x y : F) (hn : n ≠ 0)
    (h : y^2=x*(x-n)*(x+3*n)) (hx : x=0) :
    point n x y hn h=kernelPoint n hn := by
  subst x
  have hy : y=0 := (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp (by simpa using h)
  subst y
  rfl

private theorem collision_x (n x₁ x₂ : F) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0)
    (hx : x₁ ≠ x₂) (h : Ximage n x₁=Ximage n x₂) : x₂= -3*n^2/x₁ := by
  have hh : (x₁-x₂)*(x₁*x₂+3*n^2)=0 := by
    calc
      _ = (x₁*x₂)*(Ximage n x₁-Ximage n x₂) := by
        change (x₁-x₂)*(x₁*x₂+3*n^2)=
          (x₁*x₂)*((x₁+2*n-3*n^2/x₁)-(x₂+2*n-3*n^2/x₂))
        field_simp [hx₁,hx₂] <;> ring
      _ = 0 := by rw [h,sub_self,mul_zero]
  have hp : x₁*x₂+3*n^2=0 := (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hx)
  apply (eq_div_iff hx₁).2
  linear_combination hp

private theorem oriented_translation (n x y : F) (hn : n ≠ 0) (hx : x ≠ 0)
    (he : y^2=x*(x-n)*(x+3*n)) :
    ∃ z : F, ∃ hz : z^2=(-3*n^2/x)*((-3*n^2/x)-n)*((-3*n^2/x)+3*n),
      point n x y hn he+kernelPoint n hn=point n (-3*n^2/x) z hn hz := by
  let b := -3*n^2
  let X := b/x
  let Y := -b*y/x^2
  have hY : Y^2=X*(X-n)*(X+3*n) := by
    calc
      _ = (b^2/x^4)*y^2 := by dsimp [Y]; ring
      _ = _ := by rw [he]; dsimp [X,b]; field_simp [hx] <;> ring
  refine ⟨Y,hY,?_⟩
  exact actual_add_root_point n x y 0 X Y hn
    (by simpa only [sub_zero] using hx) he (by simp) hY
    (by dsimp [X,b,rootDerivative]; ring)
    (by dsimp [Y,b,rootDerivative]; ring)

theorem actual_add_of_image_collision
    (n x₁ y₁ x₂ y₂ : F) (hn : n ≠ 0)
    (he₁ : y₁^2=x₁*(x₁-n)*(x₁+3*n)) (he₂ : y₂^2=x₂*(x₂-n)*(x₂+3*n))
    (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx : x₁ ≠ x₂)
    (hXX : Ximage n x₁=Ximage n x₂) :
    literalMap n hn (point n x₁ y₁ hn he₁+point n x₂ y₂ hn he₂)=
      literalMap n hn (point n x₁ y₁ hn he₁)+literalMap n hn (point n x₂ y₂ hn he₂) := by
  let P := point n x₁ y₁ hn he₁
  let Q := point n x₂ y₂ hn he₂
  let T := kernelPoint n hn
  change literalMap n hn (P+Q)=literalMap n hn P+literalMap n hn Q
  obtain ⟨z,hz,ht⟩ := oriented_translation n x₁ y₁ hn hx₁ he₁
  have hx' := collision_x n x₁ x₂ hx₁ hx₂ hx hXX
  have hor : Q=P+T ∨ Q=-(P+T) := by
    change Q=point n x₁ y₁ hn he₁+kernelPoint n hn ∨
      Q=-(point n x₁ y₁ hn he₁+kernelPoint n hn)
    rw [ht]
    unfold Q point
    exact Point.X_eq_iff.mp hx'
  rcases hor with hq|hq
  · rw [hq,←add_assoc,actual_image_translation,actual_image_translation]
    exact actual_add_self n x₁ y₁ hn hx₁ he₁
  · apply actual_add_sum_kernel
    calc
      P+Q = -T := by rw [hq]; abel
      _ = T := kernel_neg n hn

/-- The actual point map with signed ordinate is additive for every pair.
Disjoint cases: infinity/kernel; same source abscissa (diagonal or
vertical); unequal source with a target-abscissa collision; true secant. -/
theorem literal_addition (n : F) (hn : n ≠ 0) : LiteralAddition n hn := by
  intro P Q
  cases P with
  | zero => exact actual_add_left_zero n hn Q
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => exact actual_add_right_zero n hn (.some x₁ y₁ h₁)
    | some x₂ y₂ h₂ =>
      have he₁ := (curve_equation n x₁ y₁).mp h₁.left
      have he₂ := (curve_equation n x₂ y₂).mp h₂.left
      let P := point n x₁ y₁ hn he₁
      let Q := point n x₂ y₂ hn he₂
      change literalMap n hn (P+Q)=literalMap n hn P+literalMap n hn Q
      by_cases hx₁ : x₁=0
      · have hP : P=kernelPoint n hn := affine_zero_x n x₁ y₁ hn he₁ hx₁
        rw [hP]
        exact actual_add_left_kernel n hn Q
      · by_cases hx₂ : x₂=0
        · have hQ : Q=kernelPoint n hn := affine_zero_x n x₂ y₂ hn he₂ hx₂
          rw [hQ]
          exact actual_add_right_kernel n hn P
        · by_cases hx : x₁=x₂
          · have hQ : Q=P ∨ Q= -P := by
              unfold P Q point
              exact Point.X_eq_iff.mp hx.symm
            rcases hQ with hQ|hQ
            · rw [hQ]
              exact actual_add_self n x₁ y₁ hn hx₁ he₁
            · rw [hQ]
              exact actual_add_vertical n hn P
          · by_cases hXX : Ximage n x₁=Ximage n x₂
            · exact actual_add_of_image_collision n x₁ y₁ x₂ y₂ hn he₁ he₂ hx₁ hx₂ hx hXX
            · exact actual_add_distinct_nonkernel n x₁ y₁ x₂ y₂ hn he₁ he₂ hx₁ hx₂ hx hXX

end OriginalCasselsLiteralIsogenyAddition318

#print axioms OriginalCasselsLiteralIsogenyAddition318.actual_add_of_image_collision
#print axioms OriginalCasselsLiteralIsogenyAddition318.literal_addition
