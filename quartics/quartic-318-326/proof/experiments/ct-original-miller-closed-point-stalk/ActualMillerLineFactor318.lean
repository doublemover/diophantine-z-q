module
public import ActualTwoDescentEllipticFieldCoordinates318
public import ActualTwoDescentDoublingCoordinates318
public import Mathlib.Tactic.LinearCombination
import all ActualTwoDescentEllipticModel318
public section
noncomputable section

namespace ActualMillerLineFactor318

open Polynomial
open ActualTwoDescentEllipticModel318 ActualTwoDescentEllipticFieldCoordinates318
open ActualTwoDescentDoublingCoordinates318

variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]
  [DecidableEq K] [DecidableEq L]

/-- The unit-value domain: no field convention for dividing by zero is used. -/
def ratioUnit (a b : K) : Option K :=
  if a = 0 ∨ b = 0 then none else some (a / b)

private theorem map_zero_iff (f : K →+* L) (x : K) : f x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply f.injective
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero f

theorem ratioUnit_map (f : K →+* L) (a b : K) :
    ratioUnit (f a) (f b) = (ratioUnit a b).map f := by
  by_cases h : a = 0 ∨ b = 0
  · simp only [ratioUnit, map_zero_iff f, if_pos h, Option.map_none]
  · simp only [ratioUnit, map_zero_iff f, if_neg h, Option.map_some, map_div₀]

/-- Literal scalar chart formula for a normalized addition factor.
Vertical uses x(R)-x(P), and nonvertical uses the negative of the
usual y-line so that its t=-x/y leading coefficient is +1.
This is a partial evaluation, not a rational function divisor theorem. -/
def affineFactor (n x₁ y₁ x₂ y₂ u v : K) : Option K :=
  if x₁ = x₂ ∧ y₁ = -y₂ then
    ratioUnit (u - x₁) 1
  else
    let a := (curve n).toAffine.slope x₁ x₂ y₁ y₂
    ratioUnit (a * (u - x₁) + y₁ - v) (u - (curve n).toAffine.addX x₁ x₂ a)

theorem affineFactor_map (f : K →+* L) (n x₁ y₁ x₂ y₂ u v : K) :
    affineFactor (f n) (f x₁) (f y₁) (f x₂) (f y₂) (f u) (f v) =
      (affineFactor n x₁ y₁ x₂ y₂ u v).map f := by
  have hInv : (f x₁ = f x₂ ∧ f y₁ = -(f y₂)) ↔ (x₁ = x₂ ∧ y₁ = -y₂) := by
    rw [← map_neg]
    exact ⟨fun h => ⟨f.injective h.1, f.injective h.2⟩,
      fun h => ⟨congrArg f h.1, congrArg f h.2⟩⟩
  by_cases hv : x₁ = x₂ ∧ y₁ = -y₂
  · simpa only [affineFactor, if_pos (hInv.mpr hv), if_pos hv, map_sub, map_one] using
      (ratioUnit_map f (u - x₁) 1)
  · have h₀ : ¬(f x₁ = f x₂ ∧ f y₁ = -(f y₂)) := fun h => hv (hInv.mp h)
    simpa only [affineFactor, if_neg h₀, if_neg hv, actual_slope_map, actual_addX_map,
      map_sub, map_add, map_mul] using
      (ratioUnit_map f (((curve n).toAffine.slope x₁ x₂ y₁ y₂) * (u - x₁) + y₁ - v)
        (u - (curve n).toAffine.addX x₁ x₂ ((curve n).toAffine.slope x₁ x₂ y₁ y₂)))

/-- Actual affine E_n-point evaluator, with no arbitrary value at infinity or
on the zero/pole set. The constant factor at O in an input is 1. -/
def millerStep (n : K) : Point n → Point n → Point n → Option K
  | _, _, .zero => none
  | .zero, _, .some _ _ _ => some 1
  | .some _ _ _, .zero, .some _ _ _ => some 1
  | .some x₁ y₁ _, .some x₂ y₂ _, .some u v _ => affineFactor n x₁ y₁ x₂ y₂ u v

/-- Actual nonvertical secant/tangent unit-domain formula. The three
x-exclusions imply that the numerator cannot vanish: the evaluations
of Mathlib's literal cubic intersection polynomial give the contradiction. -/
theorem affineFactor_noncollision (n x₁ y₁ x₂ y₂ u v : K)
    (h₁ : (curve n).toAffine.Equation x₁ y₁) (h₂ : (curve n).toAffine.Equation x₂ y₂)
    (hR : (curve n).toAffine.Equation u v) (hInv : ¬(x₁ = x₂ ∧ y₁ = -y₂))
    (h₁u : u ≠ x₁) (h₂u : u ≠ x₂)
    (h₃u : u ≠ (curve n).toAffine.addX x₁ x₂ ((curve n).toAffine.slope x₁ x₂ y₁ y₂)) :
    affineFactor n x₁ y₁ x₂ y₂ u v =
      some (((curve n).toAffine.slope x₁ x₂ y₁ y₂ * (u - x₁) + y₁ - v) /
        (u - (curve n).toAffine.addX x₁ x₂ ((curve n).toAffine.slope x₁ x₂ y₁ y₂))) := by
  let W := (curve n).toAffine
  let a := W.slope x₁ x₂ y₁ y₂
  have hNum : a * (u - x₁) + y₁ - v ≠ 0 := by
    intro hzero
    have hv : a * (u - x₁) + y₁ = v := sub_eq_zero.mp hzero
    have hInv' : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
      simpa only [W, curve_negY] using hInv
    have hEval : (W.addPolynomial x₁ y₁ a).eval u = 0 := by
      simp only [WeierstrassCurve.Affine.addPolynomial, WeierstrassCurve.Affine.linePolynomial,
        WeierstrassCurve.Affine.polynomial, eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow]
      rw [hv, add_mul, ← add_assoc]
      exact (W.equation_iff' u v).mp hR
    have he := congrArg (fun p : Polynomial K => p.eval u) (W.addPolynomial_slope h₁ h₂ hInv')
    change (W.addPolynomial x₁ y₁ a).eval u =
      (-((X - C x₁) * (X - C x₂) * (X - C (W.addX x₁ x₂ a)))).eval u at he
    rw [hEval] at he
    simp only [eval_neg, eval_mul, eval_sub, eval_X, eval_C] at he
    exact (neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h₁u) (sub_ne_zero.mpr h₂u))
        (sub_ne_zero.mpr h₃u))) he.symm
  unfold affineFactor
  rw [if_neg hInv]
  change ratioUnit (a * (u - x₁) + y₁ - v) (u - W.addX x₁ x₂ a) = _
  simp only [ratioUnit, if_neg (not_or.mpr ⟨hNum, sub_ne_zero.mpr h₃u⟩)]

/-- The exact dyadic noncollision factor on the project's curve;
x([2]P) and the tangent are the already verified native coordinates. -/
theorem affineFactor_double_noncollision (n x y u v : K)
    (hP : (curve n).toAffine.Equation x y) (hR : (curve n).toAffine.Equation u v)
    (hy : y ≠ 0) (hu : u ≠ x) (h₂u : u ≠ doubleX n x y) :
    affineFactor n x y x y u v =
      some ((tangent n x y * (u - x) + y - v) / (u - doubleX n x y)) := by
  have hInv : ¬(x = x ∧ y = -y) := by
    rintro ⟨_, h⟩
    exact hy (by linear_combination h / 2)
  have hAdd := actual_addX_double n x y hy
  have hAddU : u ≠ (curve n).toAffine.addX x x ((curve n).toAffine.slope x x y y) := by
    rw [hAdd]
    exact h₂u
  have h := affineFactor_noncollision n x y x y u v hP hP hR hInv hu hu hAddU
  rw [hAdd, actual_tangent n x y hy] at h
  exact h

theorem affineFactor_vertical (n x₁ y₁ x₂ y₂ u v : K)
    (hx : x₁ = x₂) (hy : y₁ = -y₂) (hu : u ≠ x₁) :
    affineFactor n x₁ y₁ x₂ y₂ u v = some (u - x₁) := by
  simp only [affineFactor, if_pos ⟨hx, hy⟩, ratioUnit,
    if_neg (not_or.mpr ⟨sub_ne_zero.mpr hu, one_ne_zero⟩), div_one]

theorem millerStep_double_point (n x y u v : K) (hn : n ≠ 0)
    (hP : y^2 = x * (x - n) * (x + 3*n)) (hR : v^2 = u * (u - n) * (u + 3*n))
    (hy : y ≠ 0) (hu : u ≠ x) (h₂u : u ≠ doubleX n x y) :
    millerStep n (point n x y hn hP) (point n x y hn hP) (point n u v hn hR) =
      some ((tangent n x y * (u - x) + y - v) / (u - doubleX n x y)) :=
  affineFactor_double_noncollision n x y u v
    ((curve_equation n x y).mpr hP) ((curve_equation n u v).mpr hR) hy hu h₂u

end ActualMillerLineFactor318
