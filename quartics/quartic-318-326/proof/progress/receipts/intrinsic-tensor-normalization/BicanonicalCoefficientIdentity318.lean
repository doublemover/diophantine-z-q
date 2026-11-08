module
public import Mathlib.Tactic.Ring
public section
namespace BicanonicalCoefficientIdentity318
variable {S : Type*} [CommRing S]

/-- Clearing only the other-branch denominator preserves the ramified
point: the squared differential coefficient agrees on the whole chart. -/
theorem finite_cleared (P D d t a C k z : S)
    (hP : (t-a)*D=C*P) (hD : D*d=1) (hz : t-a=k*z^2) :
    P*(4*C*k*d)=(2*k*z)^2 := by
  calc
    P*(4*C*k*d)=4*k*((C*P)*d) := by ring
    _=4*k*((t-a)*(D*d)) := by rw [←hP]; ring
    _=(2*k*z)^2 := by rw [hD,mul_one,hz]; ring
end BicanonicalCoefficientIdentity318
