module
public import ActualTwoDescentNonexceptionalGaloisComparison318
public section
noncomputable section
namespace ActualTwoDescentFirstTorsionGeometricHalf318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentScalarSquareRoots318 ActualTwoDescentHalfFlipTranslations318
open ActualTwoDescentHalvingGroup318 ActualTwoDescentGaloisFixedRational318
open ActualTwoDescentTorsionKummerValues318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_first_half_roots (n : ℚ) (hn : n ≠ 0) (a : Qbar) (ha : a^2=algebraMap ℚ Qbar n) :
    (0 : Qbar)^2=algebraMap ℚ Qbar n-algebraMap ℚ Qbar n ∧
    (2*a)^2=algebraMap ℚ Qbar n+3*algebraMap ℚ Qbar n := by
  constructor
  · ring
  · rw [mul_pow,ha]; ring

/-- The actual(n,0) torsion point has its explicit half in Q(sqrt(n)). -/
lemma actual_first_torsion_half (n : ℚ) (hn : n ≠ 0) (a : Qbar) (ha : a^2=algebraMap ℚ Qbar n) :
    let Q := rootHalf _ _ a 0 (2*a) (rational_parameter_ne n hn) ha
      (actual_first_half_roots n hn a ha).1 (actual_first_half_roots n hn a ha).2
    Q+Q=rationalPointMap n hn (firstTorsion n hn) := by
  apply actual_half_add_self _ _ _ a 0 (2*a) (rational_parameter_ne n hn) (by ring)
    ha (actual_first_half_roots n hn a ha).1 (actual_first_half_roots n hn a ha).2
  simp only [mul_zero,zero_mul,map_zero,neg_zero]

end ActualTwoDescentFirstTorsionGeometricHalf318
