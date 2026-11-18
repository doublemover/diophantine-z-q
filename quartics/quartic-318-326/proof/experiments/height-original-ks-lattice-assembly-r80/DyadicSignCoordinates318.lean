module
public import Mathlib.Tactic
public section
namespace DyadicSignCoordinates318

/-- Boolean signs (false = +1); the half-gap is an integer, not invert(2). -/
def s (b : Bool) : ℤ := if b then -1 else 1
def gap (i j : Bool) : ℤ := (s i - s j) / 2

variable {R : Type*} [CommRing R]

/-- Formula in the integral finite-chart generators: for r=u+2h and u'=s(j)u,
the signed r is u' + 2h'. No division is performed in R. -/
theorem finite_half (i j : Bool) (u h : R) :
    (s i : R) * (u + 2*h) =
      (s j : R)*u + 2*((s i : R)*h + (gap i j : R)*u) := by
  cases i <;> cases j <;> norm_num [s, gap] <;> ring

theorem finite_translate (i j : Bool) (u w : R) :
    (s i : R)*(u+1+w) - (s j : R)*u - 1 =
      (s i : R)*w + ((s i : R)-(s j : R))*u + ((s i : R)-1) := by
  ring

/-- i is the ratio sign (the product of the two original root signs).
The normalized reciprocal half-coordinate transforms integrally as well. -/
theorem reciprocal_half (i : Bool) (h : R) :
    (s i : R)*(1+2*h) = 1+2*((s i : R)*h + (gap i false : R)) := by
  simpa [s] using (finite_half i false (1:R) h)

theorem reciprocal_translate (i j : Bool) (x w : R) :
    (s i : R)*(1+x+w)-1-(s j : R)*x =
      (s i : R)*w + ((s i : R)-(s j : R))*x + ((s i : R)-1) := by
  ring

theorem scaled_twist {K : Type*} [Field K] (a u c t : K)
    (hu : u^2 = t-c) : (a*u)^2 = a^2*(t-c) := by
  rw [mul_pow, hu]

end DyadicSignCoordinates318
