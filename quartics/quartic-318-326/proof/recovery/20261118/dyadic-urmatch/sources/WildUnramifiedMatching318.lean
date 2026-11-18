module
public import Mathlib.Tactic
public section
namespace WildUnramifiedMatching318
variable {F : Type*} [Field F]
theorem cubic_shift (p k d : F) :
 (1+2*p)*(1-d+2*p)+(1-k+2*p)*p^2=
 2*(p+1)^3-(1+k)*(p+1)^2+2*(k-d)*(p+1)-(k-d) := by ring
end WildUnramifiedMatching318
