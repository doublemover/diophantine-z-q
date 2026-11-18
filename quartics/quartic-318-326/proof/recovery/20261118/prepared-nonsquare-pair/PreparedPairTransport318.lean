module
public import TwoTwistPointRealization318
public section
namespace PreparedPairTransport318
open NormalizedPolePoints318 TwoTwistPointRealization318

/-- Transport an actual pole pair, not just a local square or an order bound. -/
def transport {b : ℚ} (P : PointPair b) (X Z : ℚ) (hX : X ≠ 0) (hZ : Z ≠ 0)
    (hc : 1 - b*X^2/17 = (1-b/17)*Z^2) : PointPair (b*X^2) where
  parameter := P.parameter*X^2
  s := P.s*X^2*Z
  y₁ := P.y₁*X^3
  y₂ := P.y₂*X^9*Z^3
  s_ne := mul_ne_zero (mul_ne_zero P.s_ne (pow_ne_zero _ hX)) hZ
  first := by rw [mul_pow,P.first]; ring
  second := by rw [mul_pow,mul_pow,P.second,hc]; ring

/-- Both model identifications are exact with the tautological class representatives.
This realizes the source structure, not an assertion of squarefree chosen n. -/
def asRealization {b : ℚ} (P : PointPair b) : Realization b where
  β := 17*b
  θ := (17*b)^2*(1-b/17)
  c := 1
  d := 1
  n := P.parameter
  c_ne := one_ne_zero
  d_ne := one_ne_zero
  first_class := by ring
  second_class := by ring
  first := { root := 1, ordinate := P.y₁, root_ne := one_ne_zero,
             equation := by simpa using P.first }
  second := { root := P.s, ordinate := P.y₂, root_ne := P.s_ne,
              equation := P.second }

def seedB : ℚ := 1193493611520/227988105361
def a : ℚ := 1297/532
def w : ℚ := 17*(48/691)*(14/691)
def Y : ℚ := 149622419334526725/150568768
def u : ℚ := 2-51*(48/691)^2

/-- Literal nonzero-ordinate seed; all constants are exact rationals. -/
def seed : PointPair seedB where
  parameter := 17*seedB / a^2
  s := 17*seedB / a
  y₁ := w^3*Y/a^3
  y₂ := (17*seedB)^4*seedB*u/a^3
  s_ne := by norm_num [seedB,a]
  first := by norm_num [seedB,a,w,Y]
  second := by norm_num [seedB,a,u]

theorem seed_ordinates_ne : seed.y₁ ≠ 0 ∧ seed.y₂ ≠ 0 := by
  norm_num [seed,seedB,a,w,Y,u]
end PreparedPairTransport318
