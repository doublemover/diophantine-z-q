module
public import PreparedIntegerSource318
public section
noncomputable section
namespace TwoTwistPointRealization318
open NormalizedPolePoints318
set_option maxHeartbeats 0

/-- An actual rational point on the original simultaneous-twist family,
with its nonzero abscissa in the specified squareclass. No rank statement
or point on a different CM model is substituted here. -/
structure SquareclassPoint (β n : ℚ) where
  root : ℚ
  ordinate : ℚ
  root_ne : root≠0
  equation : ordinate^2=(β*root^2)*(β*root^2-n)*(β*root^2+3*n)

/-- The two squareclass identifications are literal rational equalities at
the actual source pole b. The choice of n must be shared by both curves. -/
structure Realization (b : ℚ) where
  β : ℚ
  θ : ℚ
  c : ℚ
  d : ℚ
  n : ℚ
  c_ne : c≠0
  d_ne : d≠0
  first_class : 17*b=β*c^2
  second_class : (17*b)^2*(1-b/17)=θ*d^2
  first : SquareclassPoint β n
  second : SquareclassPoint β (n*θ)

/-- The exact two scaling factors recover one shared parameter E and
abscissas B and B*s². This is the missing model-conversion step after the
simultaneous realization theorem, not a proof of that theorem. -/
@[expose] def Realization.pointPair {b : ℚ} (R : Realization b) : PointPair b where
  parameter := R.n*(R.c/R.first.root)^2
  s := R.second.root*R.d/R.first.root
  y₁ := R.first.ordinate*(R.c/R.first.root)^3
  y₂ := R.second.ordinate*(R.c*R.d/R.first.root)^3
  s_ne := div_ne_zero (mul_ne_zero R.second.root_ne R.d_ne) R.first.root_ne
  first := by
    rw [mul_pow,R.first.equation,R.first_class]
    field_simp [R.first.root_ne] <;> ring
  second := by
    rw [mul_pow,R.second.equation,R.second_class,R.first_class]
    field_simp [R.first.root_ne] <;> ring

/-- The shared parameter is fixed by the first curve's scaling, and the
second abscissa scale retains the original V rather than a free twist. -/
lemma pointPair_parameter {b : ℚ} (R : Realization b) :
    R.pointPair.parameter=R.n*(R.c/R.first.root)^2 := rfl

lemma pointPair_second_scale {b : ℚ} (R : Realization b) :
    R.pointPair.parameter*((17*b)^2*(1-b/17))=
      (R.n*R.θ)*(R.c*R.d/R.first.root)^2 := by
  rw [pointPair_parameter,R.second_class]
  ring

/-- The resulting literal pole certificate uses the same b. -/
def Realization.certificate {b : ℚ} (hb : b≠0) (R : Realization b) : Certificate b :=
  R.pointPair.certificate hb

/-- The equal-twist case is allowed: one point supplies both occurrences.
There is no artificial distinctness or nonzero-ordinate restriction. -/
def equalTwist (b β c d n : ℚ) (hc : c≠0) (hd : d≠0)
    (hB : 17*b=β*c^2) (hV : (17*b)^2*(1-b/17)=d^2)
    (P : SquareclassPoint β n) : Realization b where
  β := β
  θ := 1
  c := c
  d := d
  n := n
  c_ne := hc
  d_ne := hd
  first_class := hB
  second_class := by simpa using hV
  first := P
  second := by simpa using P

end TwoTwistPointRealization318
