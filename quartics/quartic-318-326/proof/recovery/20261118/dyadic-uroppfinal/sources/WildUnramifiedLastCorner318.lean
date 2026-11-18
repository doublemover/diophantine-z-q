module
public import Mathlib.Tactic
public section
namespace WildUnramifiedLastCorner318
variable {F : Type*} [Field F]
theorem norm_identity (u x t a d : F) :
   a*u*(1+t^2)+(a*x+d)*(1+t^2)^2=
      (1+t^2)*(a*(u+x)+d+(a*x+d)*t^2) := by ring
end WildUnramifiedLastCorner318
