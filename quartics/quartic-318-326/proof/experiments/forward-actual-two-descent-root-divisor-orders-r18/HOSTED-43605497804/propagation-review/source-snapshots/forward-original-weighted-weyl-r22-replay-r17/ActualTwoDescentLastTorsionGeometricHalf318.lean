module
public import ActualTwoDescentFirstTorsionGaloisComparison318
public section
noncomputable section
namespace ActualTwoDescentLastTorsionGeometricHalf318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentAlgebraicClosureHalving318
open ActualTwoDescentHalfFlipTranslations318 ActualTwoDescentHalvingGroup318
open ActualTwoDescentGaloisFixedRational318 ActualTwoDescentActualTorsionPoint318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_last_half_roots (n : ℚ) (u v : Qbar) (hu : u^2=3) (hv : v^2= -algebraMap ℚ Qbar n) :
    (u*v)^2=algebraMap ℚ Qbar (-3*n) ∧
    (2*v)^2=algebraMap ℚ Qbar (-3*n)-algebraMap ℚ Qbar n ∧
    (0 : Qbar)^2=algebraMap ℚ Qbar (-3*n)+3*algebraMap ℚ Qbar n := by
  simp only [mul_pow,hu,hv,map_mul,map_neg,map_ofNat]
  constructor
  · ring
  constructor <;> ring

/-- Actual(-3n,0) half in the compositum of Q(sqrt(3)) and Q(sqrt(-n)). -/
lemma actual_last_torsion_half (n : ℚ) (hn : n ≠ 0) (u v : Qbar) (hu : u^2=3) (hv : v^2= -algebraMap ℚ Qbar n) :
    let Q := rootHalf _ _ (u*v) (2*v) 0 (rational_parameter_ne n hn)
      (actual_last_half_roots n u v hu hv).1 (actual_last_half_roots n u v hu hv).2.1
      (actual_last_half_roots n u v hu hv).2.2
    Q+Q=rationalPointMap n hn (torsionPoint n hn) := by
  apply actual_half_add_self _ _ _ (u*v) (2*v) 0 (rational_parameter_ne n hn)
    (by simp only [map_mul,map_neg,map_ofNat]; ring)
    (actual_last_half_roots n u v hu hv).1 (actual_last_half_roots n u v hu hv).2.1
    (actual_last_half_roots n u v hu hv).2.2
  simp only [mul_zero,map_zero,neg_zero]

end ActualTwoDescentLastTorsionGeometricHalf318
