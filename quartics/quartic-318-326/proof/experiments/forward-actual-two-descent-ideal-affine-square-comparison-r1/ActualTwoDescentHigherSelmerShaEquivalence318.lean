module
public import ActualTwoDescentHigherRationalImage318
public section
noncomputable section
namespace ActualTwoDescentHigherSelmerShaEquivalence318
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
open ActualTwoDescentHigherKummerHom318 ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318
open ActualTwoDescentHigherFullLifting318 ActualTwoDescentGeometricPowerTorsion318
open ActualTwoDescentFullCocycleRestriction318 ActualTwoDescentGeometricPointTransport318
open ActualTwoDescentSquareClassFieldMap318
variable {L : Type} [Field L] [CharZero L] [DecidableEq L]
local instance : DecidableEq (AlgebraicClosure L) := Classical.decEq _
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

open ActualTwoDescentActualHigherSelmer318 ActualTwoDescentActualShaPower318
open ActualTwoDescentHigherSelmerToSha318 ActualTwoDescentHigherRationalImage318

/-- Exact higher Selmer/rational-image quotient is the SAME actual Sha[2^k]. -/
def higherSelmerShaEquiv (n : ℚ) (hn : n ≠ 0) (k : ℕ) :
    actualHigherSelmer n hn k ⧸ (higherRationalHom n hn k).range ≃+ actualShaPower n hn k := by
  have e := QuotientAddGroup.quotientKerEquivOfSurjective (higherSelmerToSha n hn k)
    (actual_higher_selmer_sha_surjective n hn k)
  rw [actual_higher_selmer_sha_kernel] at e
  exact e

end ActualTwoDescentHigherSelmerShaEquivalence318
