module
public import Mathlib.Tactic
public section
open scoped BigOperators

namespace SelectedMarkedNormalization318
variable {S T : Type*} [CommRing S] [CommRing T]

abbrev abscissa (c : Sˣ) (x : S) : S := (↑c⁻¹:S)*x
abbrev ordinateSquare (c Y : Sˣ) : Sˣ := (c⁻¹)^3*Y^2
abbrev recoveryScale (c d Y : Sˣ) : Sˣ := c*d*Y⁻¹

/-- Divide the actual marked equation by the cube of the short-model square
ratio. This identity holds in a nonreduced ring as well. -/
theorem normalized_equation (a b x y : S) (c : Sˣ)
    (h : y^2 = x^3+((c:S)^2*a)*x+(c:S)^3*b) :
    (↑c⁻¹:S)^3*y^2 = (abscissa c x)^3+a*abscissa c x+b := by
  have h₂ : (↑c⁻¹:S)^2*(c:S)^2 = 1 := by rw [← mul_pow,Units.inv_mul,one_pow]
  have h₃ : (↑c⁻¹:S)^3*(c:S)^3 = 1 := by rw [← mul_pow,Units.inv_mul,one_pow]
  have h₂' : (↑c⁻¹:S)^3*(c:S)^2 = (↑c⁻¹:S) := by
    calc
      _ = (↑c⁻¹:S)*((↑c⁻¹:S)^2*(c:S)^2) := by ring
      _ = _ := by rw [h₂,mul_one]
  calc
    _ = (↑c⁻¹:S)^3*x^3 + ((↑c⁻¹:S)^3*(c:S)^2)*a*x +
        ((↑c⁻¹:S)^3*(c:S)^3)*b := by rw [h]; ring
    _ = _ := by rw [h₂',h₃]; unfold abscissa; ring

theorem scale_sq (c d Y : Sˣ) (hd : d = ordinateSquare c Y) :
    recoveryScale c d Y ^ 2 = d*c⁻¹ := by
  rw [hd]
  unfold recoveryScale ordinateSquare
  group

theorem scale_y (c d Y : Sˣ) (hd : d = ordinateSquare c Y) :
    recoveryScale c d Y ^ 3 * Y = d^2 := by
  rw [hd]
  unfold recoveryScale ordinateSquare
  group

theorem scale_x (c d Y : Sˣ) (x : S) (hd : d = ordinateSquare c Y) :
    (recoveryScale c d Y : S)^2*x = (d:S)*abscissa c x := by
  have h := congrArg (fun u : Sˣ => (u:S)) (scale_sq c d Y hd)
  simp only [Units.val_pow_eq_pow_val,Units.val_mul] at h
  rw [h,mul_assoc] <;> rfl

theorem scale_coeff (c d Y : Sˣ) (hd : d = ordinateSquare c Y) :
    recoveryScale c d Y ^ 4 * c^2 = d^2 ∧
    recoveryScale c d Y ^ 6 * c^3 = d^3 := by
  constructor
  · calc
      _ = (recoveryScale c d Y ^ 2)^2 * c^2 := by rw [←pow_mul] <;> rfl
      _ = _ := by rw [scale_sq c d Y hd]; group
  · calc
      _ = (recoveryScale c d Y ^ 2)^3 * c^3 := by rw [←pow_mul] <;> rfl
      _ = _ := by rw [scale_sq c d Y hd]; group

theorem abscissa_map (f : S →+* T) (c : Sˣ) (x : S) :
    f (abscissa c x) = abscissa (Units.map f.toMonoidHom c) (f x) := by
  change f ((↑c⁻¹:S)*x) = _
  rw [map_mul] <;> rfl

theorem abscissa_transition (c r : Sˣ) (x : S) :
    abscissa (r^2*c) ((r:S)^2*x) = abscissa c x := by
  have h : (r^2*c)⁻¹*r^2 = c⁻¹ := by group
  simpa only [abscissa,Units.val_mul,Units.val_pow_eq_pow_val,mul_assoc] using
    congrArg (fun u : Sˣ => (u:S)*x) h

/-- On a genuine transition with weights 2 and 3, the fixed twist is unchanged
and the recovery scale composed with the transition is the old scale. -/
theorem ordinate_transition (c Y r : Sˣ) :
    ordinateSquare (r^2*c) (r^3*Y) = ordinateSquare c Y := by
  unfold ordinateSquare
  group

theorem scale_transition (c d Y r : Sˣ) :
    recoveryScale (r^2*c) d (r^3*Y) * r = recoveryScale c d Y := by
  unfold recoveryScale
  group
end SelectedMarkedNormalization318

#print axioms SelectedMarkedNormalization318.normalized_equation
#print axioms SelectedMarkedNormalization318.scale_coeff
#print axioms SelectedMarkedNormalization318.scale_transition
