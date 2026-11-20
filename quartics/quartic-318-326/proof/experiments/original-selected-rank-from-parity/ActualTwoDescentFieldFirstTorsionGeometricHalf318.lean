module
public import ActualTwoDescentFieldNonexceptionalGaloisComparison318
public section
noncomputable section
namespace ActualTwoDescentFieldFirstTorsionGeometricHalf318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldScalarSquareRoots318 ActualTwoDescentFieldHalfFlipTranslations318
open ActualTwoDescentHalvingGroup318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentTorsionKummerValues318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_first_half_roots (n : F) (hn : n ≠ 0) (a : Qbar) (ha : a^2=algebraMap F Qbar n) :
    (0 : Qbar)^2=algebraMap F Qbar n-algebraMap F Qbar n ∧
    (2*a)^2=algebraMap F Qbar n+3*algebraMap F Qbar n := by
  constructor
  · ring
  · rw [mul_pow,ha]; ring

/-- The actual(n,0) torsion point has its explicit half in the quadratic root extension. -/
lemma actual_first_torsion_half (n : F) (hn : n ≠ 0) (a : Qbar) (ha : a^2=algebraMap F Qbar n) :
    let Q := rootHalf _ _ a 0 (2*a) (rational_parameter_ne n hn) ha
      (actual_first_half_roots n hn a ha).1 (actual_first_half_roots n hn a ha).2
    Q+Q=rationalPointMap n hn (firstTorsion n hn) := by
  apply actual_half_add_self _ _ _ a 0 (2*a) (rational_parameter_ne n hn) (by ring)
    ha (actual_first_half_roots n hn a ha).1 (actual_first_half_roots n hn a ha).2
  simp only [mul_zero,zero_mul,map_zero,neg_zero]

end ActualTwoDescentFieldFirstTorsionGeometricHalf318
