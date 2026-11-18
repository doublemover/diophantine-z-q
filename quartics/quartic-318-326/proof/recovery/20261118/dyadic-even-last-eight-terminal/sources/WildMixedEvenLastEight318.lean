module
public import Mathlib.Tactic
public section
namespace WildMixedEvenLastEight318
variable {K : Type*} [Field K]
theorem split_exponent (s alpha beta delta X Y : K) :
    s^4 * (alpha*(s*X)+beta*(s*Y)+delta*s)^6 =
      s^2 * (s^8*(alpha*X+beta*Y+delta)^6) := by ring
theorem factored_direction (w W k : K) :
    (w*W)*(w*W+w*k)=w^2*(W*(W+k)) := by ring
end WildMixedEvenLastEight318
