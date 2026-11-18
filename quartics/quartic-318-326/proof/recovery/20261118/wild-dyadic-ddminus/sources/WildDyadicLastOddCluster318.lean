module
public import Mathlib.Tactic
public section
namespace WildDyadicLastOddCluster318
variable {F : Type*} [Field F] [CharZero F]

theorem split_equation (X Y e : F) :
  (X+e)^2+(Y-X)*(X+e)-2401*X*Y =
    e*(e+X+Y)-2400*X*Y := by ring

theorem crossing_exponent (X E V : F) :
    X^6*(X*V-X*E-X)^6=X^2*(X^10*(V-E-1)^6) := by ring

theorem etale_constant : (1:ℤ)-4*86 = -343 := by norm_num
end WildDyadicLastOddCluster318
