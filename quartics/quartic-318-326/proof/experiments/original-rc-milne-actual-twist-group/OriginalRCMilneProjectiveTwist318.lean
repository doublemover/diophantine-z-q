module
public import OriginalRCMilneSplitQuadratic318
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

public section

namespace OriginalRCMilneProjectiveTwist318

variable {F : Type*} [Field F] [CharZero F]

/-- Homogeneous equation of the literal original projective E_d.
The identity section is [0:1:0]. -/
@[expose] def equation (d X Y Z : F) : F :=
  Y^2*Z-X*(X-d*Z)*(X+3*d*Z)

/-- Forward s-coordinate isomorphism E_d → E_(kd), s²=k.
No translation; this preserves the same projective identity. -/
theorem scaled_equation (d k s X Y Z : F) (hs : s^2 = k) :
    equation (k*d) (s^2*X) (s^3*Y) Z = s^6*equation d X Y Z := by
  rw [← hs]
  unfold equation
  ring

theorem scale_ordered_root (s X Y Z : F) :
    ((-s)^2*X,(-s)^3*Y,Z) = (s^2*X,-(s^3*Y),Z) := by
  apply Prod.ext
  · ring
  · apply Prod.ext
    · ring
    · rfl

theorem inverse_scaling (s X Y Z : F) (hs0 : s ≠ 0) :
    (s⁻¹^2*(s^2*X),s⁻¹^3*(s^3*Y),Z) = (X,Y,Z) := by
  have hX : s⁻¹^2*(s^2*X) = X := by field_simp [hs0] <;> ring
  have hY : s⁻¹^3*(s^3*Y) = Y := by field_simp [hs0] <;> ring
  rw [hX,hY]

theorem scale_origin (s : F) : (s^2*0,s^3*1,(0:F)) = (0,s^3,0) := by simp

/-- On the usual open y ≠ 0, the rational invariant differential
dx/(2y) of the literal original equation has exactly this pullback.
The geometric identification of primitive Néron generators is external. -/
theorem differential_multiplier (s y dx : F) (hs0 : s ≠ 0) (hy : y ≠ 0) :
    (s^2*dx)/(2*(s^3*y)) = s⁻¹*(dx/(2*y)) := by
  field_simp [hs0,hy] <;> ring

/-- Two-by-two determinant of the literal normalized Lie map.
The forward twist's second tangent coordinate has multiplier s⁻¹.
Applying an integral twist chart (or its inverse) absorbs only a unit. -/
theorem sum_diff_lie_determinant (s : F) :
    1*(-s⁻¹)-1*s⁻¹ = -(2:F)*s⁻¹ := by ring

end OriginalRCMilneProjectiveTwist318

#print axioms OriginalRCMilneProjectiveTwist318.scaled_equation
#print axioms OriginalRCMilneProjectiveTwist318.differential_multiplier
