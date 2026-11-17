module
public import ActualTwoDescentPrimarySelmerShaKernel318
public section
noncomputable section
namespace ActualTwoDescentPrimarySelmerShaExactSequence318
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
open ActualTwoDescentPowerTorsionBoundaries318 ActualTwoDescentHigherKummerHom318
open ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318
open ActualTwoDescentPrimaryGeometricBoundary318 ActualTwoDescentFiniteLevelIntoPrimary318
open ActualTwoDescentPrimaryFullClass318 ActualTwoDescentActualPrimarySelmer318
open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentHigherSelmerIntoPrimary318
open ActualTwoDescentPrimarySelmerFiniteLevels318 ActualTwoDescentHigherRationalImage318

open ActualTwoDescentPrimarySelmerToSha318 ActualTwoDescentPrimarySelmerShaSurjectivity318
open ActualTwoDescentPrimarySelmerShaKernel318 ActualTwoDescentActualPrimaryRationalImage318
open ActualTwoDescentActualShaPrimary318

/-- Exact full primary Selmer/rational-image quotient identifies with ACTUAL full primary Sha. -/
def primarySelmerShaEquiv (n : ℚ) (hn : n ≠ 0) :
    actualPrimarySelmer n hn ⧸ rationalPrimaryImage n hn ≃+ Additive (actualShaPrimary n hn) := by
  have e := QuotientAddGroup.quotientKerEquivOfSurjective (primarySelmerToSha n hn)
    (actual_primary_selmer_sha_surjective n hn)
  rw [actual_primary_selmer_sha_kernel] at e
  exact e

end ActualTwoDescentPrimarySelmerShaExactSequence318
