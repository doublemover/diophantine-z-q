module
public import QuarticOptimization
public section
namespace ScalarJacobi
variable {K : Type*} [CommRing K]

def residual (D k m h r : K) : K :=
  (h*r)^2-k^2*r^2-2*m*h*r-k^2*h^2-D

theorem first_curve_identity (D k m h r : K) :
    (h*(h*r-m)-k^2*r)^2-k^2*(h^4-D) =
      (h^2-k^2)*residual D k m h r+h^2*(m^2-k^4+D) := by
  unfold residual
  ring

theorem second_curve_identity (D k m h r : K) :
    (k^2*h-r*(h*r-m))^2-k^2*(r^4-D) =
      (r^2-k^2)*residual D k m h r+r^2*(m^2-k^4+D) := by
  unfold residual
  ring

theorem nonzero_real (D k m h r : ℝ) (hD : 0 < D)
    (hQ : residual D k m h r = 0) : h ≠ 0 ∧ r ≠ 0 := by
  constructor
  · intro hh
    have hs : 0 ≤ (k*r)^2 := sq_nonneg _
    simp only [residual, hh] at hQ
    nlinarith
  · intro hr
    have hs : 0 ≤ (k*h)^2 := sq_nonneg _
    simp only [residual, hr] at hQ
    nlinarith
end ScalarJacobi
