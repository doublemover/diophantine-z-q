module
public import OriginalLargePrimeDivisorCount318
public section
noncomputable section
namespace OriginalLinearNormEliminant318
set_option maxHeartbeats 3500000

/-- Exact unpadded linear/quadratic eliminant for the exceptional second
pair. Its sum-of-squares form controls actual zero offsets over Z. -/
@[expose] def eliminant (t x z dx dz : ℤ) : ℤ := (dx*z-dz*x)^2+t^2*dx^2

lemma bezout (t x z dx dz h : ℤ) :
    eliminant t x z dx dz=dx^2*((z+h*dz)^2+t^2)-
      (2*(dx*z-dz*x)*dz+dz^2*(x+h*dx))*(x+h*dx) := by
  dsimp [eliminant]
  ring

lemma divisor (t x z dx dz h m : ℤ) (hx : m∣x+h*dx)
    (hg : m∣(z+h*dz)^2+t^2) : m∣eliminant t x z dx dz := by
  rw [bezout t x z dx dz h]
  exact dvd_sub (dvd_mul_of_dvd_right hg _) (dvd_mul_of_dvd_right hx _)

/-- For nonzero t and nonzero transverse linear coefficient, EVERY
integer offset has nonzero eliminant. No exceptional zero locus remains
on this branch, and no real-solvability or positivity assumption is supplied. -/
theorem positive (t x z dx dz : ℤ) (ht : t≠0) (hd : dx≠0) :
    0<eliminant t x z dx dz := by
  have hh : 0<t^2*dx^2 := mul_pos (sq_pos_of_ne_zero ht) (sq_pos_of_ne_zero hd)
  have hs := sq_nonneg (dx*z-dz*x)
  dsimp [eliminant]
  linarith

/-- The only integer zero offsets when the linear coefficient vanishes
are precisely the unchanged axis x=0, provided the other coefficient is
nonzero. This is the original exceptional plane, not a whole fiber dropped
from the count. -/
theorem zero_iff_axis (t x z dz : ℤ) (hdz : dz≠0) :
    eliminant t x z 0 dz=0 ↔ x=0 := by
  simp only [eliminant,zero_mul,zero_sub,zero_pow (by decide : (2:ℕ)≠0),mul_zero,add_zero,
    neg_sq,mul_pow]
  constructor
  · intro he
    have hx : x^2=0 := (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ hdz)
    exact pow_eq_zero hx
  · intro hx; simp [hx]

end OriginalLinearNormEliminant318
