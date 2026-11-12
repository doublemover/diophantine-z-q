module
public import ActualTwoDescentFieldFirstTorsionGaloisComparison318
public section
noncomputable section
namespace ActualTwoDescentFieldLastTorsionGeometricHalf318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldHalfFlipTranslations318 ActualTwoDescentHalvingGroup318
open ActualTwoDescentFieldGaloisFixedRational318 ActualTwoDescentActualTorsionPoint318
local instance : DecidableEq Qbar := Classical.decEq _

lemma actual_last_half_roots (n : F) (u v : Qbar) (hu : u^2=3) (hv : v^2= -algebraMap F Qbar n) :
    (u*v)^2=algebraMap F Qbar (-3*n) ∧
    (2*v)^2=algebraMap F Qbar (-3*n)-algebraMap F Qbar n ∧
    (0 : Qbar)^2=algebraMap F Qbar (-3*n)+3*algebraMap F Qbar n := by
  simp only [mul_pow,hu,hv,map_mul,map_neg,map_ofNat]
  constructor
  · ring
  constructor <;> ring

/-- Actual(-3n,0) half in the compositum of the two displayed quadratic root extensions. -/
lemma actual_last_torsion_half (n : F) (hn : n ≠ 0) (u v : Qbar) (hu : u^2=3) (hv : v^2= -algebraMap F Qbar n) :
    let Q := rootHalf _ _ (u*v) (2*v) 0 (rational_parameter_ne n hn)
      (actual_last_half_roots n u v hu hv).1 (actual_last_half_roots n u v hu hv).2.1
      (actual_last_half_roots n u v hu hv).2.2
    Q+Q=rationalPointMap n hn (torsionPoint n hn) := by
  apply actual_half_add_self _ _ _ (u*v) (2*v) 0 (rational_parameter_ne n hn)
    (by simp only [map_mul,map_neg,map_ofNat]; ring)
    (actual_last_half_roots n u v hu hv).1 (actual_last_half_roots n u v hu hv).2.1
    (actual_last_half_roots n u v hu hv).2.2
  simp only [mul_zero,map_zero,neg_zero]

end ActualTwoDescentFieldLastTorsionGeometricHalf318
