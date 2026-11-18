module
public import Mathlib.Tactic
public section
namespace WildMixedParityOpposite318
variable {F : Type*} [Field F]
theorem corner_shift (x s j a b : F) :
 (x+s*j)^2+b*(x+s*j)-(x^2+a*x)=s^2*j^2+(2*s*x+b*s)*j+(b-a)*x := by ring
end WildMixedParityOpposite318
