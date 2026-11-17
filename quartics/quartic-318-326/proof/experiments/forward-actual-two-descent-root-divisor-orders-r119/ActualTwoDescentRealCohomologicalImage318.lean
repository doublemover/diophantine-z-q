module
public import ActualTwoDescentPadicCohomologicalImage318
public section
noncomputable section
namespace ActualTwoDescentRealCohomologicalImage318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentSquareClassQuotient318
open ActualTwoDescentFieldContinuousTorsionCoordinates318 ActualTwoDescentFieldActualCohomologicalImage318
open ActualTwoDescentFieldImageCriterion318 ActualTwoDescentLocalImageSubgroup318

/-- Genuine real elliptic connecting image, with infinity and all rational roots retained. -/
theorem actual_real_cohomological_image (n : ℝ) (hn : n ≠ 0) (z : SquareClass ℝ × SquareClass ℝ) :
    (continuousTorsionSquareclasses n hn).symm z ∈ rationalCocycleImage n hn ↔ z ∈ actualKummerImage n hn :=
  actual_field_image_criterion n hn z

end ActualTwoDescentRealCohomologicalImage318
