module
public import OriginalAffineSieveEliminants318
public section
noncomputable section
namespace OriginalEliminantLeadingTerm318
open OriginalQuadraticEliminant318 Polynomial
set_option maxHeartbeats 5000000

@[expose] def scaledEliminant (a b c r d e f s : ℤ) : Polynomial ℤ :=
  eliminant (C a) (C b*X) (C c*X^2+C r) (C d) (C e*X) (C f*X^2+C s)
@[expose] def middleCoefficient (a b c r d e f s : ℤ) : ℤ :=
  2*a^2*f*s-a*b*e*s-2*a*c*d*s-2*a*r*d*f+a*r*e^2+b^2*d*s-b*r*d*e+2*c*r*d^2

/-- Exact polynomial certificate for the eliminant along a scaled
remaining-coordinate direction, not just sampled evaluations. -/
lemma scaled_identity (a b c r d e f s : ℤ) :
    scaledEliminant a b c r d e f s=
      C (eliminant a b c d e f)*X^4+C (middleCoefficient a b c r d e f s)*X^2+
        C ((a*s-r*d)^2) := by
  simp only [scaledEliminant,eliminant,middleCoefficient,map_add,map_sub,map_mul,map_pow,map_ofNat]
  ring

lemma fourth_coefficient (a b c r d e f s : ℤ) :
    (scaledEliminant a b c r d e f s).coeff 4=eliminant a b c d e f := by
  rw [scaled_identity]
  simp

lemma scaled_nonzero (a b c r d e f s : ℤ) (h : eliminant a b c d e f≠0) :
    scaledEliminant a b c r d e f s≠0 := by
  intro hz
  have hh := fourth_coefficient a b c r d e f s
  rw [hz,Polynomial.coeff_zero] at hh
  exact h hh.symm

/-- Leading coefficient for firstP against either original norm factor.
The actual cross minor, not a matrix determinant of a different lattice,
is the nonvanishing input exposed to the basis producer. -/
lemma first_leading (κ dw ew dx ex : ℤ) :
    eliminant (κ*dw^2) (2*κ*dw*ew) (κ*ew^2)
      (dx^2) (2*dx*ex) (ex^2)=κ^2*(dw*ex-dx*ew)^4 := by
  dsimp [eliminant]
  ring

/-- Leading coefficient for secondP against the x norm factor. The z
terms cancel exactly; t=-2 is explicitly exceptional, not hidden. -/
lemma second_leading_x (κ t dw ew dx ex dz ez : ℤ) :
    eliminant (κ*(t+2)*dw^2-2*dx*dz)
      (2*κ*(t+2)*dw*ew-2*(dx*ez+ex*dz))
      (κ*(t+2)*ew^2-2*ex*ez)
      (dx^2) (2*dx*ex) (ex^2)=κ^2*(t+2)^2*(dw*ex-dx*ew)^4 := by
  dsimp [eliminant]
  ring

lemma second_leading_z (κ t dw ew dx ex dz ez : ℤ) :
    eliminant (κ*(t+2)*dw^2-2*dx*dz)
      (2*κ*(t+2)*dw*ew-2*(dx*ez+ex*dz))
      (κ*(t+2)*ew^2-2*ex*ez)
      (dz^2) (2*dz*ez) (ez^2)=κ^2*(t+2)^2*(dw*ez-dz*ew)^4 := by
  dsimp [eliminant]
  ring

/-- The regular second eliminant is proved nonzero as a polynomial;
this does not yet bound the number of points where its value is zero. -/
theorem regular_second_nonzero (κ t dw ew dx ex dz ez : ℤ)
    (hκ : κ≠0) (ht : t+2≠0) (hminor : dw*ex-dx*ew≠0) :
    scaledEliminant (κ*(t+2)*dw^2-2*dx*dz)
      (2*κ*(t+2)*dw*ew-2*(dx*ez+ex*dz))
      (κ*(t+2)*ew^2-2*ex*ez) 0
      (dx^2) (2*dx*ex) (ex^2) (t^2)≠0 := by
  apply scaled_nonzero
  rw [second_leading_x]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hκ) (pow_ne_zero _ ht)) (pow_ne_zero _ hminor)

theorem first_nonzero (κ t dw ew dx ex : ℤ) (hκ : κ≠0) (hminor : dw*ex-dx*ew≠0) :
    scaledEliminant (κ*dw^2) (2*κ*dw*ew) (κ*ew^2) (2*t)
      (dx^2) (2*dx*ex) (ex^2) (t^2)≠0 := by
  apply scaled_nonzero
  rw [first_leading]
  exact mul_ne_zero (pow_ne_zero _ hκ) (pow_ne_zero _ hminor)

end OriginalEliminantLeadingTerm318
