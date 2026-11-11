module
public import ActualTwoDescentActualShaTwoSurjectivity318
public section
noncomputable section
namespace ActualTwoDescentActualShaObstructionEquivalence318
set_option maxHeartbeats 16000000

variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldGaloisTwoTorsion318 ActualTwoDescentFieldHalvingCocycle318
open ActualTwoDescentFieldHalvingChoiceIndependence318 ActualTwoDescentFieldGaloisLocallyConstant318
open ActualTwoDescentFieldContinuousGaloisCocycles318 ActualTwoDescentFieldActualCohomologicalImage318
open groupCohomology

open ActualTwoDescentActualShaDefinition318 ActualTwoDescentSelmerToActualSha318
open ActualTwoDescentSelmerObstructionComparison318 ActualTwoDescentActualShaExactKernel318
open ActualTwoDescentActualShaTwoSurjectivity318

/-- The original concrete obstruction is now identified with ACTUAL full elliptic Tate-Shafarevich2-torsion. -/
def actualShaObstructionEquiv (n : ℚ) (hn : n ≠ 0) : SelmerObstruction n hn ≃* actualShaTwo n hn := by
  have e := QuotientGroup.quotientKerEquivOfSurjective (selmerToShaTwo n hn) (actual_selmer_sha_surjective n hn)
  rw [actual_selmer_sha_kernel] at e
  exact e

lemma actual_sha_obstruction_cardinality (n : ℚ) (hn : n ≠ 0) :
    Nat.card (actualShaTwo n hn)=Nat.card (ActualTwoDescentConcreteLocalObstruction318.LocalObstruction n hn) := by
  rw [←Nat.card_congr (actualShaObstructionEquiv n hn).toEquiv]
  exact actual_selmer_obstruction_card n hn

end ActualTwoDescentActualShaObstructionEquivalence318
