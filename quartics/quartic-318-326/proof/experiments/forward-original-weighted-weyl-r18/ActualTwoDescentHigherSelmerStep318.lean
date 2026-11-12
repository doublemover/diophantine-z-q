module
public import ActualTwoDescentHigherRestrictionStep318
public section
noncomputable section
namespace ActualTwoDescentHigherSelmerStep318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldHalvingCocycle318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentFullEllipticHOneKernel318
open groupCohomology

open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentHigherCohomologyStep318
open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherSelmerShaComparison318

/-- Genuine higher Selmer transitions preserve the independently defined all-place conditions. -/
def higherSelmerStep (n : ℚ) (hn : n ≠ 0) (k : ℕ) : actualHigherSelmer n hn k →+ actualHigherSelmer n hn (k+1) where
  toFun x := ⟨higherCohomologyStep n hn k x.val,by
    apply (actual_higher_selmer_iff_sha n hn (k+1) _).mpr
    rw [actual_higher_step_full_class]
    exact (actual_higher_selmer_iff_sha n hn k x.val).mp x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

end ActualTwoDescentHigherSelmerStep318
