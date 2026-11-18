module
public import Mathlib.Tactic
public section
namespace WildUnramifiedEvenSix318
variable {F : Type*} [Field F]
theorem cubed_crossing (p X Y a b g : F) :
 p*(a*(p*X)+b*(p*Y)+g*p)^3=p^2*(p^2*(a*X+b*Y+g)^3) := by ring
end WildUnramifiedEvenSix318
