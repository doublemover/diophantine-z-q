module
public import OriginalUniformSparseSmoothChart318

/-! The same literal sparse family on the ordinary reciprocal projective
chart. This does not exchange the two Cowan square-root sheets. -/

public section
namespace OriginalUniformSparseReciprocalChart318

open OriginalUniformSparseSmoothChart318 (eqVal)
variable {R : Type*} [CommRing R]

@[expose] def reverse (s t z : R) : R :=
  s^2 + (-2*(s*t)*s)*z + (-10*(s*t)*(s*t-5))*z^3 +
    (-2*(s*t)*t*(5-s*t)^2)*z^5 + t^2*(5-s*t)^3*z^6

/-- Literal Laurent overlap, in any ring where xz=1. -/
theorem reverse_laurent (s t x z : R) (h : x*z=1) :
    eqVal s t x * z^6 = reverse s t z := by
  have hp (n : ℕ) : (x*z)^n=1 := by rw [h,one_pow]
  calc
    _ = s^2*(x*z)^6 + (-2*(s*t)*s)*(x*z)^5*z +
        (-10*(s*t)*(s*t-5))*(x*z)^3*z^3 +
        (-2*(s*t)*t*(5-s*t)^2)*(x*z)^1*z^5 +
        t^2*(5-s*t)^3*z^6 := by unfold eqVal; ring
    _ = _ := by rw [hp, hp, hp, hp]; unfold reverse; ring

theorem overlap (s t x y z : R) (hx : x*z=1)
    (hy : y^2=eqVal s t x) :
    (y*z^3)^2=reverse s t z := by
  calc
    _ = y^2*z^6 := by ring
    _ = _ := by rw [hy,reverse_laurent s t x z hx]

/-- The reciprocal substitution and its actual inverse agree on y, not just
on the projected parameter. Both sides live on the same sparse sheet. -/
theorem overlap_inverse (x y z : R) (hx : x*z=1) : (y*z^3)*x^3=y := by
  calc
    _ = y*(x*z)^3 := by ring
    _ = y := by rw [hx,one_pow,mul_one]

theorem origin (s t : R) : reverse s t 0=s^2 := by unfold reverse; ring

/-- Both sections at infinity are honest (Y=±s), with invertible y-Jacobian
when 2 and the original leading square s² are units. -/
theorem infinity_sections (s t : R) (h2 : IsUnit (2:R)) (hs : IsUnit s) :
    s^2=reverse s t 0 ∧ (-s)^2=reverse s t 0 ∧
      IsUnit (2*s) ∧ IsUnit (2*(-s)) := by
  rw [origin,neg_sq]
  exact ⟨rfl,rfl,h2.mul hs,h2.mul hs.neg⟩

end OriginalUniformSparseReciprocalChart318

#print axioms OriginalUniformSparseReciprocalChart318.overlap
#print axioms OriginalUniformSparseReciprocalChart318.infinity_sections
