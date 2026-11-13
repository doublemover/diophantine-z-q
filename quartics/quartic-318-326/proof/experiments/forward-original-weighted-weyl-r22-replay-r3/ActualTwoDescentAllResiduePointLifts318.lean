module
public import ActualTwoDescentNonexceptionalPointLift318
public section
noncomputable section
namespace ActualTwoDescentAllResiduePointLifts318
set_option maxHeartbeats 16000000

open ActualTwoDescentFiniteEllipticModel318 ActualTwoDescentIntegralPointLiftData318
open ActualTwoDescentExceptionalPointLifts318 ActualTwoDescentNonexceptionalPointLift318
variable {p : ℕ} [Fact p.Prime] [NeZero (2 : ZMod p)] [NeZero (3 : ZMod p)]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- Every ACTUAL residue elliptic point has an ACTUAL p-adic point with the same adjusted coordinate residues. -/
def actual_residue_point_lift (hp2 : p ≠ 2) (n : ℤ) (hn : (n : ZMod p) ≠ 0)
    (P : Point (n : ZMod p)) : IntegralPointLift n hn P := by
  cases P with
  | zero => exact infinityLift n hn
  | some x y h =>
    by_cases hx : x=0
    · subst x; exact zeroRootLift n hn y h
    by_cases hx1 : x=(n : ZMod p)
    · subst x; exact firstRootLift n hn y h
    by_cases hx3 : x= -3*(n : ZMod p)
    · subst x; exact secondRootLift n hn y h
    exact nonexceptionalLift hp2 n hn x y h hx (sub_ne_zero.mpr hx1)
      (by intro he; apply hx3; linear_combination he)

end ActualTwoDescentAllResiduePointLifts318
