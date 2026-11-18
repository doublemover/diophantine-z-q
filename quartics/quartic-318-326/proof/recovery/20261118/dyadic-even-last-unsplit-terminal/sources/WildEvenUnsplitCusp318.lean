module
public import Mathlib.Tactic
public section
namespace WildEvenUnsplitCusp318
variable {F : Type*} [Field F]
theorem cusp_transform (q P Z f m a b : F) :
 f*(q^2*Z)^2+q*m*(q*P)*(q^2*Z)+q*a*(q*P)^3+q^2*b*(q*P)^2
  =q^4*(f*Z^2+m*P*Z+a*P^3+b*P^2) := by ring
end WildEvenUnsplitCusp318
