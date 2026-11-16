module
public import ActualTwoDescentHigherSelmerDirectedSystem318
public section
noncomputable section
namespace ActualTwoDescentHigherSelmerIntoPrimary318
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

open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentActualPrimarySelmer318
open ActualTwoDescentFiniteLevelIntoPrimary318 ActualTwoDescentPrimarySelmerFiniteLevels318
open ActualTwoDescentHigherSelmerDirectedSystem318 ActualTwoDescentHigherCohomologyDirectedSystem318

def higherSelmerIntoPrimary (n : ℚ) (hn : n ≠ 0) (k : ℕ) : actualHigherSelmer n hn k →+ actualPrimarySelmer n hn where
  toFun x := ⟨powerIntoPrimaryHOne n hn k x.val,(actual_primary_selmer_finite_level_iff n hn k x.val).mpr x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x.val y.val)

lemma actual_selmer_primary_compatible (n : ℚ) (hn : n ≠ 0) (i j : ℕ) (h : i ≤ j) (x : actualHigherSelmer n hn i) :
    higherSelmerIntoPrimary n hn j (higherSelmerMap n hn i j h x)=higherSelmerIntoPrimary n hn i x :=
  Subtype.ext (actual_power_primary_compatible n hn i j h x.val)

end ActualTwoDescentHigherSelmerIntoPrimary318
