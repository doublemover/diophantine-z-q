module
public import Mathlib.Tactic
public section
namespace WildMixedEtaleSplit318
variable {F : Type*} [Field F] [CharZero F]
theorem cleared_etale_change (D L i S B J : F) :
    (2*D*B+(L-i)*S)^2+2*i*S*(2*D*B+(L-i)*S) -
    4*D*(D*B^2+L*S*B+J*S^2)=(L^2-i^2-4*D*J)*S^2 := by ring
theorem hidden_discriminant (t D J : F) (ht:t^2=2*D) (hJ:t^2*J=D+t+1) :
    (1+t)^2-4*D*J = -1 := by
  linear_combination ht - 2*hJ + (2*J)*ht
end WildMixedEtaleSplit318
