module
public import OriginalKleinMarkedJet318
import Mathlib.Tactic
public section
noncomputable section
namespace OriginalKleinMarkedCoordinates318
open Polynomial
inductive Row where | m105 | m70 | m42 | m30
deriving DecidableEq
def quartic (a b c d e : ℤ) : ℤ[X] := C a*X^4+C b*X^3+C c*X^2+C d*X+C e
def N : Row → Bool → ℤ[X]
  | .m105, false => quartic (-10976) 153664 (-713440) 921984 (-395136)
  | .m105, true => quartic (-395136) 921984 (-713440) 153664 (-10976)
  | .m70, false => quartic (-10976) (-87808) (-109760) 263424 (-98784)
  | .m70, true => quartic (-98784) 263424 (-109760) (-87808) (-10976)
  | .m42, false => quartic (-10976) 0 (-21952) 0 (-10976)
  | .m42, true => quartic (-10976) 0 (-21952) 0 (-10976)
  | .m30, false => quartic (-10976) (-21952) (-54880) (-43904) (-43904)
  | .m30, true => quartic (-43904) (-43904) (-54880) (-21952) (-10976)
def F : Row → Bool → ℤ[X]
  | .m105, false => quartic (-43) 2 505 12 (-1548)
  | .m105, true => quartic (-1548) 12 505 2 (-43)
  | .m70, false => quartic (-43) 256 (-130) (-768) (-387)
  | .m70, true => quartic (-387) (-768) (-130) 256 (-43)
  | .m42, false => quartic (-43) 600 (-986) (-600) (-43)
  | .m42, true => quartic (-43) (-600) (-986) 600 (-43)
  | .m30, false => quartic (-43) (-686) (-2915) (-1372) (-172)
  | .m30, true => quartic (-172) (-1372) (-2915) (-686) (-43)
@[expose] def b : Row → ℤ
  | .m105 => 0
  | .m70 => 32
  | .m42 => 76832
  | .m30 => -343
@[expose] def kn : Row → ℤ
  | .m105 => 4
  | .m70 => 16
  | .m42 => -16
  | .m30 => 1
@[expose] def kd : Row → ℤ
  | .m105 => 75
  | .m70 => 343
  | .m42 => 1
  | .m30 => 8
@[expose] def r0 : Row → ℤ
  | .m105 => 32
  | .m70 => 0
  | .m42 => 0
  | .m30 => 0
@[expose] def r1 : Row → ℤ
  | .m105 => 76832
  | .m70 => 76832
  | .m42 => 32
  | .m30 => 32
@[expose] def r2 : Row → ℤ
  | .m105 => -343
  | .m70 => -343
  | .m42 => -343
  | .m30 => 76832

/-- Identity over the integers, including the reciprocal chart at x = ∞.
Coefficients are not divided by 2 (or by a nonunit) in a special fibre. -/
theorem identity (m : Row) (j : Bool) :
    C (kd m)*(derivative (N m j)*F m j-N m j*derivative (F m j))^2 =
    C (kn m)*(N m j-C (r0 m)*F m j)*(N m j-C (r1 m)*F m j)*(N m j-C (r2 m)*F m j) := by
  cases m <;> cases j <;>
    simp [N,F,kd,kn,r0,r1,r2,quartic,derivative_add,derivative_mul,derivative_pow] <;> ring
end OriginalKleinMarkedCoordinates318
#print axioms OriginalKleinMarkedCoordinates318.identity
