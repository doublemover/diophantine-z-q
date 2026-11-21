module
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public section

namespace OriginalCasselsAffineChordImage318

variable {F : Type*} [Field F]

/-- Literal source form after cutting by the line y=m*x+c. -/
def cut (n m c x : F) : F :=
  x^3+(2*n-m^2)*x^2+(-3*n^2-2*m*c)*x-c^2

/-- The transformed ordinate lies on the exact target line. This is
the nonvertical residual numerator only, not a Point addition theorem. -/
theorem oriented_image_line (n m c x : F) (hc : c ≠ 0) (hx : x ≠ 0)
    (hcut : cut n m c x=0) :
    m*x+c+3*n^2*(m*x+c)/x^2=
      (m+3*n^2/c)*(x+2*n-3*n^2/x)+(c-2*n*m-3*n^2*m^2/c) := by
  calc
    _ = (m+3*n^2/c)*(x+2*n-3*n^2/x)+(c-2*n*m-3*n^2*m^2/c)
      + (-3*n^2/(c*x^2))*cut n m c x := by
      dsimp [cut]
      field_simp [hc,hx] <;> ring
    _ = _ := by rw [hcut,mul_zero,add_zero]

/-- The exact target sum of the three transformed abscissae. It covers
multiplicity at the level of the formula, not the tangent-law proof. -/
theorem transformed_vieta (n m c x₁ x₂ x₃ : F)
    (hc : c ≠ 0) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₃ : x₃ ≠ 0)
    (hsum : x₁+x₂+x₃=m^2-2*n)
    (hpair : x₁*x₂+x₁*x₃+x₂*x₃= -3*n^2-2*m*c)
    (hprod : x₁*x₂*x₃=c^2) :
    (x₁+2*n-3*n^2/x₁)+(x₂+2*n-3*n^2/x₂)+(x₃+2*n-3*n^2/x₃)=
      (m+3*n^2/c)^2+4*n := by
  have hrec : 1/x₁+1/x₂+1/x₃=(x₁*x₂+x₁*x₃+x₂*x₃)/(x₁*x₂*x₃) := by
    field_simp [hx₁,hx₂,hx₃] <;> ring
  calc
    _ = (x₁+x₂+x₃)+6*n-3*n^2*(1/x₁+1/x₂+1/x₃) := by ring
    _ = _ := by rw [hsum,hrec,hpair,hprod]; field_simp [hc] <;> ring

end OriginalCasselsAffineChordImage318

#print axioms OriginalCasselsAffineChordImage318.oriented_image_line
#print axioms OriginalCasselsAffineChordImage318.transformed_vieta
