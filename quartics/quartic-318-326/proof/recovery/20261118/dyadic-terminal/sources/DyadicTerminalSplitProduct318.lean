module
public import DyadicNormalizedCoordinates318
public section
namespace DyadicTerminalSplitProduct318

/-- Exact ramified-base identity; clearing denominators by the original
unit L (and not by the nonunit 2) will give w^6 or w^10. -/
theorem ramified_powers {R : Type*} [CommRing R] (w L : R) (hw : w^2 = -2*L) :
    w^6 = -(8:R)*L^3 ∧ w^10 = -(32:R)*L^5 := by
  constructor
  · calc
      _ = (w^2)^3 := by ring
      _ = _ := by rw [hw]; ring
  · calc
      _ = (w^2)^5 := by ring
      _ = _ := by rw [hw]; ring

/-- The A and B equations are the third w-chart of the actual two monic
half-root adjunctions. At the sole remaining point A is a unit; division
is only by A here. The exact integer 2401 is 49^2, not a residue lift. -/
theorem split_product {F : Type*} [Field F] (A B S G : F) (ha : A ≠ 0)
    (hA : A^2+S*A=G) (hB : B^2+S*B=2401*G) :
    let e := B/A-1-2400
    let t := 1+G/A^2
    e*(e+t+4800) = -(2400*2401:F) := by
  dsimp only
  have hnum : A*B^2-A^2*B+G*B-2401*G*A=0 := by
    linear_combination A*hB - B*hA
  calc
    _ = (A*B^2-A^2*B+G*B-2401*G*A)/A^3 - 2400*2401 := by
      field_simp [ha] <;> ring
    _ = _ := by rw [hnum]; ring

/-- After two point blowups along the crossing direction the literal
strict-transform equation has exponent 16. The coefficient multiplier
becomes a unit at the chosen point by the separate order-two calculation. -/
theorem second_divided_equation {F : Type*} [Field F] (p E V Z h : F)
    (hp : p ≠ 0) (hf : (p^2*E)*(p^2*V) = h*(p^2*Z)^10) :
    E*V=p^16*(h*Z^10) := by
  apply mul_left_cancel₀ (pow_ne_zero 4 hp)
  calc
    p^4*(E*V) = (p^2*E)*(p^2*V) := by ring
    _ = _ := hf
    _ = _ := by ring

end DyadicTerminalSplitProduct318
