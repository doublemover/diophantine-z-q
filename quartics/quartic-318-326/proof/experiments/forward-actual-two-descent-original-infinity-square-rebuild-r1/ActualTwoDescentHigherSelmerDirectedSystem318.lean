module
public import ActualTwoDescentPrimarySelmerFiniteLevels318
public section
noncomputable section
namespace ActualTwoDescentHigherSelmerDirectedSystem318
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
open ActualTwoDescentPowerValuedCocycles318 ActualTwoDescentPowerTorsionBoundaries318
open ActualTwoDescentGeometricPowerTorsion318 ActualTwoDescentFullBoundaryHom318
open ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318 ActualTwoDescentHigherFullLifting318

open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherSelmerShaComparison318
open ActualTwoDescentHigherCohomologyDirectedMaps318 ActualTwoDescentHigherCohomologyDirectedSystem318

def higherSelmerMap (n : ℚ) (hn : n ≠ 0) (i j : ℕ) (h : i ≤ j) : actualHigherSelmer n hn i →+ actualHigherSelmer n hn j where
  toFun x := ⟨higherCohomologyMap n hn i j h x.val,by
    apply (actual_higher_selmer_iff_sha n hn j _).mpr
    rw [actual_higher_map_full_class]
    exact (actual_higher_selmer_iff_sha n hn i x.val).mp x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

instance actual_higher_selmer_directed (n : ℚ) (hn : n ≠ 0) :
    DirectedSystem (fun k => actualHigherSelmer n hn k) (fun i j h => higherSelmerMap n hn i j h) where
  map_self x := Subtype.ext (DirectedSystem.map_self (f:=fun i j h => higherCohomologyMap n hn i j h) x.val)
  map_map hij hjk x := Subtype.ext (DirectedSystem.map_map (f:=fun i j h => higherCohomologyMap n hn i j h) hij hjk x.val)

end ActualTwoDescentHigherSelmerDirectedSystem318
