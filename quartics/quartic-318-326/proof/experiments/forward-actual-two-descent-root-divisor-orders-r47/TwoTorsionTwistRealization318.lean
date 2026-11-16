module
public import TwoTwistPointRealization318
public section
noncomputable section
namespace TwoTorsionTwistRealization318
open TwoTwistPointRealization318 NormalizedPolePoints318

/-- The squareclass root is 1 and the abscissa is the literal root x = beta.
The abscissa may vanish when beta = 0; SquareclassPoint requires only a nonzero
root, not a nonzero abscissa or ordinate. -/
def diagonalPoint (β : ℚ) : SquareclassPoint β β where
  root := 1
  ordinate := 0
  root_ne := one_ne_zero
  equation := by ring

/-- When the exact source twist V is a nonzero square, explicit two-torsion
points supply BOTH point obligations, on the original pole and common n. -/
def squareTwist (b d : ℚ) (hd : d ≠ 0)
    (hV : (17*b)^2*(1-b/17) = d^2) : Realization b :=
  equalTwist b (17*b) 1 d (17*b) one_ne_zero hd (by ring) hV
    (diagonalPoint (17*b))

/-- A concrete rational complement square produces the exact V-square witness.
This removes an arbitrary squareclass witness, but does not assert that every
source pole has a square complement. -/
def ofSquareComplement (b r : ℚ) (hb : b ≠ 0) (hr : r ≠ 0)
    (h : 1-b/17 = r^2) : Realization b :=
  squareTwist b (17*b*r) (mul_ne_zero (mul_ne_zero (by norm_num) hb) hr) (by
    rw [h]
    ring)

/-- Conversion consumes the same pole b and the already-checked literal
certificate constructor, not a point on an unrelated elliptic model. -/
def squareComplementCertificate (b r : ℚ) (hb : b ≠ 0) (hr : r ≠ 0)
    (h : 1-b/17 = r^2) : Certificate b :=
  (ofSquareComplement b r hb hr h).certificate hb

/-- The actual positive-pole interval is inhabited by an explicit rational
family, not merely a conditional squareclass record. -/
theorem parameterizedPole_bounds (r : ℚ) (hr : r ≠ 0) (hsmall : r^2 < 1) :
    0 < 17*(1-r^2) ∧ 17*(1-r^2) < 17 := by
  have hpos : 0 < r^2 := sq_pos_of_ne_zero hr
  constructor <;> nlinarith

/-- An actual literal source-pole certificate throughout this rational family.
Choosing all four source poles in this family at one CRT index remains open. -/
def parameterizedCertificate (r : ℚ) (hr : r ≠ 0) (hsmall : r^2 < 1) :
    Certificate (17*(1-r^2)) :=
  squareComplementCertificate (17*(1-r^2)) r
    (ne_of_gt (parameterizedPole_bounds r hr hsmall).1) hr (by ring)

end TwoTorsionTwistRealization318
