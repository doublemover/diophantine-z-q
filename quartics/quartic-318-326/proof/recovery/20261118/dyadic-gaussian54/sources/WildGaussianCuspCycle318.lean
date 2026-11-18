module
public import Mathlib.Tactic
public section
namespace WildGaussianCuspCycle318
variable {F : Type*} [Field F]
theorem first_cycle (p P Z M B N : F) :
 (p^2*Z)^2+p^3*M*(p*P)*(p^2*Z)+p*B*(p*P)^3+p^18*N*(p*P)^2
  =p^4*(Z^2+p^2*M*P*Z+(B*P+p^16*N)*P^2) := by ring
end WildGaussianCuspCycle318
