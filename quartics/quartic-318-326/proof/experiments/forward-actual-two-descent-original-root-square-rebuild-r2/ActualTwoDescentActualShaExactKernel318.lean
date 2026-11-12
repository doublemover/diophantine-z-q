module
public import ActualTwoDescentSelmerToActualSha318
public section
noncomputable section
namespace ActualTwoDescentActualShaExactKernel318
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

open ActualTwoDescentSelmerToActualSha318 ActualTwoDescentSelmerObstructionComparison318
open ActualTwoDescentFullConnectingExactness318

lemma actual_selmer_sha_kernel (n : ℚ) (hn : n ≠ 0) :
    (selmerToShaTwo n hn).ker=selmerRationalInside n hn := by
  ext χ
  change selmerToShaTwo n hn χ=1 ↔ χ.val ∈ rationalCocycleImage n hn
  rw [←actual_full_connecting_exact]
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

end ActualTwoDescentActualShaExactKernel318
