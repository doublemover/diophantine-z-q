module
public import ActualTwoDescentFieldImageCriterion318
public section
noncomputable section
namespace ActualTwoDescentPadicCohomologicalImage318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentSquareClassQuotient318
open ActualTwoDescentFieldContinuousTorsionCoordinates318 ActualTwoDescentFieldActualCohomologicalImage318
open ActualTwoDescentFieldImageCriterion318 ActualTwoDescentLocalImageSubgroup318
variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- Genuine p-adic elliptic connecting image, including p=2,3 and every reduction type. -/
theorem actual_padic_cohomological_image (n : ℚ_[p]) (hn : n ≠ 0) (z : SquareClass (ℚ_[p]) × SquareClass (ℚ_[p])) :
    (continuousTorsionSquareclasses n hn).symm z ∈ rationalCocycleImage n hn ↔ z ∈ actualKummerImage n hn :=
  actual_field_image_criterion n hn z

end ActualTwoDescentPadicCohomologicalImage318
